import asyncio
import csv
import io
import logging
import math
import os
import sqlite3
import time
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from statistics import mean
from typing import Any
from urllib.parse import quote_plus

import httpx
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ChatAction
from telegram.ext import Application, CommandHandler, ContextTypes

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("moex-signal-bot")

TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
ADMIN_CHAT_ID = os.environ.get("ADMIN_CHAT_ID", "")
DB_PATH = os.environ.get("DB_PATH", "trades.db")
SCAN_SECONDS = int(os.environ.get("SCAN_SECONDS", "60"))
SIGNAL_MIN_SCORE = float(os.environ.get("SIGNAL_MIN_SCORE", "4"))
SIGNAL_HORIZON_MINUTES = max(5, min(240, int(os.environ.get("SIGNAL_HORIZON_MINUTES", "240"))))
TARGET_PROFIT_PCT = max(0.001, min(0.50, float(os.environ.get("TARGET_PROFIT_PCT", "0.05"))))
CRYPTO_HORIZON_MINUTES = 10
CRYPTO_TARGET_PROFIT_PCT = max(0.001, min(0.50, float(os.environ.get("CRYPTO_TARGET_PROFIT_PCT", "0.05"))))
CRYPTO_LIMIT = 100

# Значение ALL означает: загрузить все активные акции с доски TQBR.
TICKER_SETTING = os.environ.get("MOEX_TICKERS", "ALL").strip().upper()
TICKERS = [] if TICKER_SETTING in ("", "ALL", "*", "ВСЕ") else [
    x.strip() for x in TICKER_SETTING.split(",") if x.strip()
]

MOEX_SECURITIES = "https://iss.moex.com/iss/engines/stock/markets/shares/boards/TQBR/securities.json"
MOEX_CANDLES = "https://iss.moex.com/iss/engines/stock/markets/shares/boards/TQBR/securities/{ticker}/candles.json"
COINGECKO_MARKETS = "https://api.coingecko.com/api/v3/coins/markets"
BINANCE_KLINES = "https://api.binance.com/api/v3/klines"
GOOGLE_NEWS_RSS = "https://news.google.com/rss/search?q={query}+акции&hl=ru&gl=RU&ceid=RU:ru"

NEGATIVE_WORDS = (
    "иск", "штраф", "дефолт", "санкци", "банкрот", "обвал", "убыт", "отзыв",
    "дивиденд отмен", "арест", "проверка", "fraud", "default", "bankruptcy",
    "sanction", "lawsuit", "downgrade",
)
COMPANY_NAMES = {
    "SBER": "Сбербанк", "GAZP": "Газпром", "LKOH": "Лукойл", "YNDX": "Яндекс",
    "ROSN": "Роснефть", "TATN": "Татнефть", "MOEX": "Московская биржа",
    "T": "Т-Банк / Т-Технологии",
    "GMKN": "Норникель", "NVTK": "Новатэк", "VTBR": "ВТБ",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def db() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("""CREATE TABLE IF NOT EXISTS trades (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        created_at TEXT NOT NULL, closed_at TEXT,
        ticker TEXT NOT NULL, side TEXT NOT NULL,
        entry REAL NOT NULL, exit REAL, target REAL NOT NULL, stop REAL NOT NULL,
        score REAL NOT NULL, status TEXT NOT NULL,
        pnl REAL, pnl_pct REAL, reason TEXT, indicators TEXT,
        news TEXT, timeframe TEXT NOT NULL DEFAULT '5m'
    )""")
    conn.execute("""CREATE TABLE IF NOT EXISTS crypto_trades (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        created_at TEXT NOT NULL, closed_at TEXT, ticker TEXT NOT NULL,
        name TEXT, entry REAL NOT NULL, exit REAL, target REAL NOT NULL,
        stop REAL NOT NULL, score REAL NOT NULL, status TEXT NOT NULL,
        pnl REAL, pnl_pct REAL, reason TEXT, indicators TEXT,
        timeframe TEXT NOT NULL DEFAULT '10m'
    )""")
    conn.commit()
    return conn


def authorized(update: Update) -> bool:
    if not ADMIN_CHAT_ID:
        return True
    return str(update.effective_chat.id) == str(ADMIN_CHAT_ID)


@dataclass
class Candle:
    ts: int
    open: float
    high: float
    low: float
    close: float
    volume: float


@dataclass
class Signal:
    ticker: str
    entry: float
    target: float
    stop: float
    score: float
    reason: str
    indicators: str
    news: str


def ema(values: list[float], period: int) -> float:
    if not values:
        return 0.0
    alpha = 2 / (period + 1)
    value = values[0]
    for item in values[1:]:
        value = alpha * item + (1 - alpha) * value
    return value


def rsi(values: list[float], period: int = 14) -> float:
    if len(values) <= period:
        return 50.0
    gains, losses = [], []
    for before, after in zip(values[-period - 1:-1], values[-period:]):
        delta = after - before
        gains.append(max(delta, 0))
        losses.append(max(-delta, 0))
    avg_gain, avg_loss = mean(gains), mean(losses)
    if avg_loss == 0:
        return 100.0 if avg_gain else 50.0
    return 100 - 100 / (1 + avg_gain / avg_loss)


def resample_candles(candles: list[Candle], minutes: int) -> list[Candle]:
    """Собирает минутные свечи MOEX в горизонт от 5 минут до 4 часов."""
    if minutes <= 1:
        return candles
    buckets: dict[int, list[Candle]] = {}
    size = minutes * 60
    for candle in candles:
        bucket = (candle.ts // size) * size
        buckets.setdefault(bucket, []).append(candle)
    result = []
    for bucket, items in sorted(buckets.items()):
        items.sort(key=lambda item: item.ts)
        result.append(Candle(bucket, items[0].open, max(item.high for item in items),
                             min(item.low for item in items), items[-1].close,
                             sum(item.volume for item in items)))
    return result


def parse_candles(payload: dict[str, Any]) -> list[Candle]:
    block = payload.get("candles", {})
    columns = block.get("columns", [])
    rows = block.get("data", [])
    index = {name: columns.index(name) for name in columns}
    required = ("begin", "open", "high", "low", "close", "volume")
    if not all(name in index for name in required):
        return []
    result = []
    for row in rows:
        try:
            if any(row[index[name]] is None for name in required):
                continue
            ts = int(datetime.fromisoformat(str(row[index["begin"]]).replace("Z", "+00:00")).timestamp())
            result.append(Candle(ts, float(row[index["open"]]), float(row[index["high"]]),
                                 float(row[index["low"]]), float(row[index["close"]]),
                                 float(row[index["volume"]] or 0)))
        except (ValueError, TypeError, OverflowError):
            continue
    return result


async def fetch_universe(client: httpx.AsyncClient) -> list[str]:
    """Получает актуальный список активных акций на доске TQBR."""
    response = await client.get(
        MOEX_SECURITIES,
        params={
            "iss.meta": "off",
            "iss.only": "securities",
            "securities.columns": "SECID,SHORTNAME,STATUS",
        },
    )
    response.raise_for_status()
    block = response.json().get("securities", {})
    columns = block.get("columns", [])
    rows = block.get("data", [])
    positions = {name: columns.index(name) for name in columns}
    result = []
    for row in rows:
        try:
            ticker = str(row[positions["SECID"]]).upper()
            name = str(row[positions["SHORTNAME"]])
            status = str(row[positions["STATUS"]]).upper()
            if ticker and status not in {"D", "DELISTED"}:
                COMPANY_NAMES.setdefault(ticker, name)
                result.append(ticker)
        except (KeyError, IndexError, TypeError):
            continue
    return sorted(set(result))


async def fetch_candles(client: httpx.AsyncClient, ticker: str) -> list[Candle]:
    end = datetime.now(timezone.utc).date()
    start = end - timedelta(days=10)
    response = await client.get(
        MOEX_CANDLES.format(ticker=ticker),
        params={"interval": 1, "from": start.isoformat(), "till": end.isoformat(), "iss.meta": "off"},
    )
    response.raise_for_status()
    candles = parse_candles(response.json())
    return resample_candles(candles, SIGNAL_HORIZON_MINUTES)[-240:]


async def fetch_news(client: httpx.AsyncClient, ticker: str) -> tuple[str, bool]:
    query = quote_plus(COMPANY_NAMES.get(ticker, ticker))
    try:
        response = await client.get(GOOGLE_NEWS_RSS.format(query=query), timeout=8)
        response.raise_for_status()
        root = ET.fromstring(response.text)
        titles = [item.text or "" for item in root.findall(".//item/title")][:5]
        negative = [title for title in titles if any(word in title.casefold() for word in NEGATIVE_WORDS)]
        if negative:
            return "Негативные заголовки: " + " | ".join(negative[:2]), True
        return ("Новости: негативных ключевых слов не обнаружено" if titles else "Новости недоступны"), False
    except (httpx.HTTPError, ET.ParseError, ValueError) as error:
        log.warning("news %s: %s", ticker, error)
        return "Новости недоступны; сигнал по новостям не подтверждён", False


async def make_signal(client: httpx.AsyncClient, ticker: str) -> Signal | None:
    candles = await fetch_candles(client, ticker)
    if len(candles) < 35:
        return None
    # Последняя свеча может быть незавершённой; используем предыдущую как последнюю закрытую.
    closed = candles[:-1] or candles
    last = closed[-1]
    closes = [c.close for c in closed]
    ema9, ema21, rsi14 = ema(closes, 9), ema(closes, 21), rsi(closes, 14)
    recent = closed[-21:-1]
    recent_high = max(c.high for c in recent)
    avg_volume = mean(c.volume for c in closed[-21:-1]) or 1
    volume_ratio = last.volume / avg_volume
    vwap_window = closed[-20:]
    vwap_den = sum(c.volume for c in vwap_window) or 1
    vwap = sum(((c.high + c.low + c.close) / 3) * c.volume for c in vwap_window) / vwap_den
    score = 0.0
    reasons = []
    if last.close > ema9 > ema21:
        score += 1.5; reasons.append("EMA9 выше EMA21")
    if last.close > vwap:
        score += 1.0; reasons.append("цена выше VWAP")
    if 52 <= rsi14 <= 72:
        score += 1.0; reasons.append(f"RSI {rsi14:.1f} в рабочей зоне")
    if volume_ratio >= 1.2:
        score += 1.5; reasons.append(f"объём {volume_ratio:.1f}x к среднему")
    if last.close > recent_high:
        score += 1.5; reasons.append("пробой локального максимума")
    if last.close > last.open:
        score += 0.5; reasons.append("положительная свеча")
    if score < SIGNAL_MIN_SCORE:
        return None
    # Новости загружаем только для технических кандидатов, иначе сканер всей биржи
    # создавал бы лишние сотни RSS-запросов.
    news, negative_news = await fetch_news(client, ticker)
    if negative_news:
        return None
    # Модельная бумажная цель/стоп; это не обещание результата.
    entry = last.close
    target = round(entry * (1 + TARGET_PROFIT_PCT), 4)
    stop = round(entry * 0.998, 4)
    indicators = f"EMA9={ema9:.4f}; EMA21={ema21:.4f}; RSI={rsi14:.1f}; VWAP={vwap:.4f}; volume_ratio={volume_ratio:.2f}"
    return Signal(ticker, entry, target, stop, score, "; ".join(reasons), indicators, news)


async def fetch_crypto_universe(client: httpx.AsyncClient) -> list[dict[str, str]]:
    response = await client.get(COINGECKO_MARKETS, params={
        "vs_currency": "usd", "order": "market_cap_desc", "per_page": CRYPTO_LIMIT,
        "page": 1, "sparkline": "false", "locale": "en",
    })
    response.raise_for_status()
    result = []
    for item in response.json():
        symbol = str(item.get("symbol", "")).upper()
        coin_id = str(item.get("id", ""))
        name = str(item.get("name", symbol))
        if symbol and coin_id and symbol not in {"USDT", "USDC", "DAI", "BUSD", "USDE"}:
            result.append({"id": coin_id, "symbol": symbol, "name": name})
    return result[:CRYPTO_LIMIT]


async def fetch_crypto_candles(client: httpx.AsyncClient, symbol: str) -> list[Candle]:
    response = await client.get(BINANCE_KLINES, params={"symbol": f"{symbol}USDT", "interval": "1m", "limit": 180})
    if response.status_code in (400, 404):
        return []
    response.raise_for_status()
    result = []
    for row in response.json():
        try:
            result.append(Candle(int(row[0] / 1000), float(row[1]), float(row[2]),
                                 float(row[3]), float(row[4]), float(row[5])))
        except (IndexError, TypeError, ValueError):
            continue
    return result


async def make_crypto_signal(client: httpx.AsyncClient, coin: dict[str, str]) -> Signal | None:
    candles = await fetch_crypto_candles(client, coin["symbol"])
    if len(candles) < 35:
        return None
    closed = candles[:-1] or candles
    last = closed[-1]
    closes = [c.close for c in closed]
    ema9, ema21, rsi14 = ema(closes, 9), ema(closes, 21), rsi(closes, 14)
    recent = closed[-21:-1]
    recent_high = max(c.high for c in recent)
    avg_volume = mean(c.volume for c in closed[-21:-1]) or 1
    volume_ratio = last.volume / avg_volume
    vwap_window = closed[-20:]
    vwap_den = sum(c.volume for c in vwap_window) or 1
    vwap = sum(((c.high + c.low + c.close) / 3) * c.volume for c in vwap_window) / vwap_den
    score = 0.0
    reasons = []
    if last.close > ema9 > ema21: score += 1.5; reasons.append("EMA9 выше EMA21")
    if last.close > vwap: score += 1.0; reasons.append("цена выше VWAP")
    if 52 <= rsi14 <= 72: score += 1.0; reasons.append(f"RSI {rsi14:.1f} в рабочей зоне")
    if volume_ratio >= 1.2: score += 1.5; reasons.append(f"объём {volume_ratio:.1f}x к среднему")
    if last.close > recent_high: score += 1.5; reasons.append("пробой локального максимума")
    if last.close > last.open: score += 0.5; reasons.append("положительная свеча")
    if score < SIGNAL_MIN_SCORE: return None
    entry = last.close
    target = entry * (1 + CRYPTO_TARGET_PROFIT_PCT)
    stop = entry * 0.998
    indicators = f"EMA9={ema9:.6g}; EMA21={ema21:.6g}; RSI={rsi14:.1f}; VWAP={vwap:.6g}; volume_ratio={volume_ratio:.2f}"
    return Signal(f"{coin['symbol']}/USDT", entry, target, stop, score, "; ".join(reasons), indicators, coin["name"])


def active_crypto_trade(conn: sqlite3.Connection, ticker: str) -> sqlite3.Row | None:
    return conn.execute("SELECT * FROM crypto_trades WHERE ticker=? AND status='OPEN' ORDER BY id DESC LIMIT 1", (ticker,)).fetchone()


def create_crypto_trade(signal: Signal) -> None:
    conn = db()
    conn.execute("""INSERT INTO crypto_trades
        (created_at,ticker,name,entry,target,stop,score,status,reason,indicators,timeframe)
        VALUES (?,?,?,?,?,?,?,?,?,?,?)""", (now_iso(), signal.ticker, signal.news, signal.entry,
        signal.target, signal.stop, signal.score, "OPEN", signal.reason, signal.indicators, "10m"))
    conn.commit(); conn.close()


def active_trade(conn: sqlite3.Connection, ticker: str) -> sqlite3.Row | None:
    return conn.execute("SELECT * FROM trades WHERE ticker=? AND status='OPEN' ORDER BY id DESC LIMIT 1", (ticker,)).fetchone()


def create_trade(signal: Signal) -> None:
    conn = db()
    conn.execute("""INSERT INTO trades
        (created_at,ticker,side,entry,target,stop,score,status,reason,indicators,news,timeframe)
        VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""", (now_iso(), signal.ticker, "BUY", signal.entry,
        signal.target, signal.stop, signal.score, "OPEN", signal.reason, signal.indicators, signal.news,
        f"{SIGNAL_HORIZON_MINUTES}m"))
    conn.commit(); conn.close()


def close_trade(row: sqlite3.Row, exit_price: float, status: str) -> None:
    pnl = exit_price - row["entry"]
    pnl_pct = pnl / row["entry"] * 100 if row["entry"] else 0
    conn = db()
    conn.execute("UPDATE trades SET closed_at=?, exit=?, pnl=?, pnl_pct=?, status=? WHERE id=?",
                 (now_iso(), exit_price, pnl, pnl_pct, status, row["id"]))
    conn.commit(); conn.close()


async def update_open_trades(client: httpx.AsyncClient) -> None:
    conn = db()
    rows = conn.execute("SELECT * FROM trades WHERE status='OPEN'").fetchall()
    conn.close()
    for row in rows:
        try:
            candles = await fetch_candles(client, row["ticker"])
            if not candles:
                continue
            price = candles[-1].close
            age = time.time() - datetime.fromisoformat(row["created_at"]).timestamp()
            if price >= row["target"]:
                close_trade(row, price, "TARGET")
            elif price <= row["stop"]:
                close_trade(row, price, "STOP")
            elif age >= SIGNAL_HORIZON_MINUTES * 60:
                close_trade(row, price, "EXPIRED")
        except (httpx.HTTPError, ValueError, IndexError) as error:
            log.warning("close %s: %s", row["ticker"], error)


def stats() -> dict[str, Any]:
    conn = db()
    total = conn.execute("SELECT COUNT(*) FROM trades WHERE status!='OPEN'").fetchone()[0]
    wins = conn.execute("SELECT COUNT(*) FROM trades WHERE status='TARGET'").fetchone()[0]
    pnl = conn.execute("SELECT COALESCE(SUM(pnl),0) FROM trades WHERE status!='OPEN'").fetchone()[0]
    avg_win = conn.execute("SELECT COALESCE(AVG(pnl),0) FROM trades WHERE pnl>0").fetchone()[0]
    avg_loss = conn.execute("SELECT COALESCE(AVG(pnl),0) FROM trades WHERE pnl<0").fetchone()[0]
    open_count = conn.execute("SELECT COUNT(*) FROM trades WHERE status='OPEN'").fetchone()[0]
    rows = conn.execute("SELECT pnl FROM trades WHERE status!='OPEN' ORDER BY id").fetchall()
    conn.close()
    equity, peak, max_dd = 0.0, 0.0, 0.0
    for row in rows:
        equity += row[0] or 0
        peak = max(peak, equity)
        max_dd = min(max_dd, equity - peak)
    return {"total": total, "wins": wins, "losses": total - wins, "win_rate": wins / total * 100 if total else 0,
            "pnl": pnl, "avg_win": avg_win, "avg_loss": avg_loss, "open": open_count, "max_dd": max_dd}


def stats_text() -> str:
    s = stats()
    return (f"Бумажная статистика MOEX {SIGNAL_HORIZON_MINUTES}m\n\nЗакрыто: {s['total']}/500\n"
            f"Прибыльных: {s['wins']} | Убыточных/истёкших: {s['losses']}\n"
            f"Win rate: {s['win_rate']:.1f}%\nСуммарный PnL: {s['pnl']:.2f} ₽\n"
            f"Средняя прибыль: {s['avg_win']:.2f} ₽\nСредний убыток: {s['avg_loss']:.2f} ₽\n"
            f"Максимальная модельная просадка: {s['max_dd']:.2f} ₽\nОткрытых сигналов: {s['open']}\n\n"
            "Все сделки виртуальные; результат не является гарантией будущей доходности.")


def export_csv() -> bytes:
    conn = db(); rows = conn.execute("SELECT * FROM trades ORDER BY id").fetchall(); conn.close()
    output = io.StringIO(); writer = csv.writer(output)
    writer.writerow(rows[0].keys() if rows else ["id", "created_at", "ticker", "status"])
    writer.writerows([tuple(row) for row in rows])
    return output.getvalue().encode("utf-8-sig")


async def update_open_crypto_trades(client: httpx.AsyncClient) -> None:
    conn = db(); rows = conn.execute("SELECT * FROM crypto_trades WHERE status='OPEN'").fetchall(); conn.close()
    for row in rows:
        try:
            candles = await fetch_crypto_candles(client, row["ticker"].split("/")[0])
            if not candles: continue
            price = candles[-1].close
            age = time.time() - datetime.fromisoformat(row["created_at"]).timestamp()
            status = "TARGET" if price >= row["target"] else "STOP" if price <= row["stop"] else "EXPIRED" if age >= 600 else None
            if status:
                pnl = price - row["entry"]
                conn = db(); conn.execute("UPDATE crypto_trades SET closed_at=?,exit=?,pnl=?,pnl_pct=?,status=? WHERE id=?",
                    (now_iso(), price, pnl, pnl / row["entry"] * 100 if row["entry"] else 0, status, row["id"])); conn.commit(); conn.close()
        except (httpx.HTTPError, ValueError, IndexError):
            continue


def crypto_stats_text() -> str:
    conn = db(); total = conn.execute("SELECT COUNT(*) FROM crypto_trades WHERE status!='OPEN'").fetchone()[0]
    wins = conn.execute("SELECT COUNT(*) FROM crypto_trades WHERE status='TARGET'").fetchone()[0]
    pnl = conn.execute("SELECT COALESCE(SUM(pnl_pct),0) FROM crypto_trades WHERE status!='OPEN'").fetchone()[0]
    opened = conn.execute("SELECT COUNT(*) FROM crypto_trades WHERE status='OPEN'").fetchone()[0]; conn.close()
    return (f"Бумажная статистика крипты 10m\n\nЗакрыто: {total}/500\n"
            f"Цель +5% достигнута: {wins}\nWin rate: {wins / total * 100 if total else 0:.1f}%\n"
            f"Сумма изменений: {pnl:.2f}%\nОткрытых сигналов: {opened}\n\nНе финансовая гарантия; сделки виртуальные.")


async def send_crypto_signal(chat_id: str, signal: Signal, context: ContextTypes.DEFAULT_TYPE) -> None:
    symbol = signal.ticker.split("/")[0]
    text = (f"КРИПТО 10M — BUY-кандидат\n\nМонета: {signal.news}\nПара: {signal.ticker}\n"
            f"Цена входа: {signal.entry:.8g} USDT\nЦель: {signal.target:.8g} USDT (+{CRYPTO_TARGET_PROFIT_PCT * 100:.1f}%)\n"
            f"Стоп: {signal.stop:.8g} USDT\nСрок: 10 минут\nОценка условий: {signal.score:.1f}\n"
            f"Причины: {signal.reason}\nИндикаторы: {signal.indicators}\n\n"
            "Статус: бумажный сигнал, не приказ к покупке")
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("Открыть график Binance", url=f"https://www.binance.com/en/trade/{symbol}_USDT")],
        [InlineKeyboardButton("Открыть график TradingView", url=f"https://www.tradingview.com/symbols/{symbol}USDT/")],
    ])
    await context.bot.send_message(chat_id=chat_id, text=text, reply_markup=keyboard)


async def crypto_scan_once(context: ContextTypes.DEFAULT_TYPE) -> None:
    async with httpx.AsyncClient(timeout=15, headers={"User-Agent": "MOEX-Crypto-Paper-Bot/1.0"}) as client:
        await update_open_crypto_trades(client)
        cache = context.application.bot_data.get("crypto_universe")
        cache_time = context.application.bot_data.get("crypto_universe_time", 0)
        if not cache or time.time() - cache_time > 3600:
            cache = await fetch_crypto_universe(client)
            context.application.bot_data["crypto_universe"] = cache
            context.application.bot_data["crypto_universe_time"] = time.time()
            log.info("Crypto universe loaded: %s top coins", len(cache))
        semaphore = asyncio.Semaphore(8)
        async def scan_coin(coin):
            try:
                conn = db(); active = active_crypto_trade(conn, f"{coin['symbol']}/USDT"); conn.close()
                if active: return None
                async with semaphore: return await make_crypto_signal(client, coin)
            except (httpx.HTTPError, ValueError, KeyError, IndexError): return None
        signals = await asyncio.gather(*(scan_coin(coin) for coin in cache))
        for signal in signals:
            if signal:
                create_crypto_trade(signal)
                if ADMIN_CHAT_ID: await send_crypto_signal(ADMIN_CHAT_ID, signal, context)


async def send_signal(chat_id: str, signal: Signal, context: ContextTypes.DEFAULT_TYPE) -> None:
    company = COMPANY_NAMES.get(signal.ticker, signal.ticker)
    text = (f"MOEX {SIGNAL_HORIZON_MINUTES}M — BUY-кандидат\n\n"
            f"Компания: {company}\nТикер: {signal.ticker}\nЦена входа: {signal.entry:.4f} ₽\n"
            f"Цель: {signal.target:.4f} ₽ (+{TARGET_PROFIT_PCT * 100:.1f}%)\n"
            f"Стоп: {signal.stop:.4f} ₽\nСрок: {SIGNAL_HORIZON_MINUTES} минут\n"
            f"Оценка условий: {signal.score:.1f}\nПричины: {signal.reason}\n"
            f"Индикаторы: {signal.indicators}\n{signal.news}\n\n"
            "Статус: бумажный сигнал, не приказ к покупке")
    ticker = quote_plus(signal.ticker)
    moex_url = f"https://www.moex.com/issue.aspx?board=TQBR&code={ticker}"
    tbank_url = f"https://www.tbank.ru/invest/stocks/{ticker}/"
    sber_url = f"https://www.sberbank.ru/ru/person/investments/stocks/{signal.ticker.lower()}"
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("Открыть график в Т‑Инвестициях", url=tbank_url)],
        [InlineKeyboardButton("Открыть график в СберИнвестициях", url=sber_url)],
        [InlineKeyboardButton("Открыть карточку на MOEX", url=moex_url)],
    ])
    await context.bot.send_message(chat_id=chat_id, text=text, reply_markup=keyboard)


async def scan_once(context: ContextTypes.DEFAULT_TYPE) -> None:
    if not ADMIN_CHAT_ID:
        log.warning("ADMIN_CHAT_ID не задан: сканирование работает, но уведомлять некого")
    async with httpx.AsyncClient(timeout=15, headers={"User-Agent": "MOEX-Paper-Signal-Bot/1.0"}) as client:
        await update_open_trades(client)
        if TICKERS:
            tickers = TICKERS
        else:
            cache = context.application.bot_data.get("moex_universe")
            cache_time = context.application.bot_data.get("moex_universe_time", 0)
            if not cache or time.time() - cache_time > 3600:
                try:
                    cache = await fetch_universe(client)
                    context.application.bot_data["moex_universe"] = cache
                    context.application.bot_data["moex_universe_time"] = time.time()
                    log.info("MOEX universe loaded: %s active TQBR shares", len(cache))
                except (httpx.HTTPError, ValueError, KeyError) as error:
                    log.warning("MOEX universe unavailable: %s", error)
                    cache = []
            tickers = cache or []

        semaphore = asyncio.Semaphore(8)
        async def scan_ticker(ticker: str):
            try:
                conn = db(); already_open = active_trade(conn, ticker); conn.close()
                if already_open:
                    return None
                async with semaphore:
                    return await make_signal(client, ticker)
            except (httpx.HTTPError, ValueError, KeyError, IndexError) as error:
                log.warning("scan %s: %s", ticker, error)
                return None

        signals = await asyncio.gather(*(scan_ticker(ticker) for ticker in tickers))
        for signal in signals:
            if signal:
                create_trade(signal)
                if ADMIN_CHAT_ID:
                    await send_signal(ADMIN_CHAT_ID, signal, context)
                log.info("paper signal %s %.4f", signal.ticker, signal.entry)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not authorized(update): return
    await update.message.reply_text("MOEX + Crypto Paper Signal Bot активен. Только виртуальные сделки.\nКоманды: /scan /crypto_scan /report /crypto_report /export /final_report")


async def scan_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not authorized(update): return
    await context.bot.send_chat_action(chat_id=update.effective_chat.id, action=ChatAction.TYPING)
    await scan_once(context)
    await update.message.reply_text("Сканирование завершено.\n\n" + stats_text())


async def crypto_scan_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not authorized(update): return
    await context.bot.send_chat_action(chat_id=update.effective_chat.id, action=ChatAction.TYPING)
    try:
        await crypto_scan_once(context)
        await update.message.reply_text("Проверка топ-100 криптовалют завершена.\n\n" + crypto_stats_text())
    except (httpx.HTTPError, ValueError, KeyError) as error:
        log.exception("crypto scan failed")
        await update.message.reply_text(f"Криптосканирование временно недоступно: {error}")


async def crypto_report(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if authorized(update): await update.message.reply_text(crypto_stats_text())


async def report(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if authorized(update): await update.message.reply_text(stats_text())


async def export_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not authorized(update): return
    await update.message.reply_document(document=io.BytesIO(export_csv()), filename="moex_paper_trades.csv", caption="История виртуальных сделок")


async def final_report(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not authorized(update): return
    s = stats()
    if s["total"] < 500:
        await update.message.reply_text(f"Пока закрыто {s['total']} из 500 сделок.\n\n{stats_text()}")
    else:
        await update.message.reply_text("500 сделок накоплены. Используйте /export и пришлите CSV для анализа стратегии.\n\n" + stats_text())


class HealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.end_headers()
        self.wfile.write(b"MOEX paper bot is running")

    def log_message(self, format, *args):
        return


def start_health_server() -> None:
    port = int(os.environ.get("PORT", "10000"))
    server = HTTPServer(("0.0.0.0", port), HealthHandler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    log.info("Health server listening on port %s", port)


async def background_scan(context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        await scan_once(context)
    except Exception:
        log.exception("background MOEX scan failed")


async def background_crypto_scan(context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        await crypto_scan_once(context)
    except Exception:
        log.exception("background crypto scan failed")


def main() -> None:
    if not TOKEN:
        raise RuntimeError("Не задана переменная TELEGRAM_BOT_TOKEN")
    db().close()
    start_health_server()
    application = Application.builder().token(TOKEN).build()
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("scan", scan_command))
    application.add_handler(CommandHandler("crypto_scan", crypto_scan_command))
    application.add_handler(CommandHandler("crypto_report", crypto_report))
    application.add_handler(CommandHandler("report", report))
    application.add_handler(CommandHandler("export", export_command))
    application.add_handler(CommandHandler("final_report", final_report))
    if application.job_queue:
        application.job_queue.run_repeating(background_scan, interval=SCAN_SECONDS, first=10)
        application.job_queue.run_repeating(background_crypto_scan, interval=600, first=30)
    else:
        log.warning("JobQueue unavailable; install python-telegram-bot[job-queue]")
    # Python 3.14 no longer creates a default event loop automatically.
    # python-telegram-bot 21.x expects one for run_polling().
    try:
        asyncio.get_event_loop()
    except RuntimeError:
        asyncio.set_event_loop(asyncio.new_event_loop())
    application.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
