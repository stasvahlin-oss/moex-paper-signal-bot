import asyncio
import csv
import io
import logging
import os
import sqlite3
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from statistics import mean
from typing import Any
from urllib.parse import quote_plus

import httpx
from telegram import Update
from telegram.constants import ChatAction
from telegram.ext import Application, CommandHandler, ContextTypes

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("moex-signal-bot")

TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
ADMIN_CHAT_ID = os.environ.get("ADMIN_CHAT_ID", "")
DB_PATH = os.environ.get("DB_PATH", "trades.db")
SCAN_SECONDS = int(os.environ.get("SCAN_SECONDS", "60"))
SIGNAL_MIN_SCORE = float(os.environ.get("SIGNAL_MIN_SCORE", "4"))

# Ликвидные инструменты TQBR по умолчанию; список можно изменить через MOEX_TICKERS.
TICKERS = [x.strip().upper() for x in os.environ.get(
    "MOEX_TICKERS", "SBER,GAZP,LKOH,YNDX,ROSN,TATN,MOEX,GMKN,NVTK,VTBR"
).split(",") if x.strip()]

MOEX_CANDLES = "https://iss.moex.com/iss/engines/stock/markets/shares/boards/TQBR/securities/{ticker}/candles.json"
GOOGLE_NEWS_RSS = "https://news.google.com/rss/search?q={query}+акции&hl=ru&gl=RU&ceid=RU:ru"

NEGATIVE_WORDS = (
    "иск", "штраф", "дефолт", "санкци", "банкрот", "обвал", "убыт", "отзыв",
    "дивиденд отмен", "арест", "проверка", "fraud", "default", "bankruptcy",
    "sanction", "lawsuit", "downgrade",
)
COMPANY_NAMES = {
    "SBER": "Сбербанк", "GAZP": "Газпром", "LKOH": "Лукойл", "YNDX": "Яндекс",
    "ROSN": "Роснефть", "TATN": "Татнефть", "MOEX": "Московская биржа",
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


async def fetch_candles(client: httpx.AsyncClient, ticker: str) -> list[Candle]:
    end = datetime.now(timezone.utc).date()
    start = end - timedelta(days=10)
    response = await client.get(
        MOEX_CANDLES.format(ticker=ticker),
        params={"interval": 5, "from": start.isoformat(), "till": end.isoformat(), "iss.meta": "off"},
    )
    response.raise_for_status()
    return parse_candles(response.json())[-120:]


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
    news, negative_news = await fetch_news(client, ticker)
    if negative_news:
        return None
    if score < SIGNAL_MIN_SCORE:
        return None
    # Модельная бумажная цель/стоп; это не обещание результата.
    entry = last.close
    target = round(entry * 1.003, 4)
    stop = round(entry * 0.998, 4)
    indicators = f"EMA9={ema9:.4f}; EMA21={ema21:.4f}; RSI={rsi14:.1f}; VWAP={vwap:.4f}; volume_ratio={volume_ratio:.2f}"
    return Signal(ticker, entry, target, stop, score, "; ".join(reasons), indicators, news)


def active_trade(conn: sqlite3.Connection, ticker: str) -> sqlite3.Row | None:
    return conn.execute("SELECT * FROM trades WHERE ticker=? AND status='OPEN' ORDER BY id DESC LIMIT 1", (ticker,)).fetchone()


def create_trade(signal: Signal) -> None:
    conn = db()
    conn.execute("""INSERT INTO trades
        (created_at,ticker,side,entry,target,stop,score,status,reason,indicators,news)
        VALUES (?,?,?,?,?,?,?,?,?,?,?)""", (now_iso(), signal.ticker, "BUY", signal.entry,
        signal.target, signal.stop, signal.score, "OPEN", signal.reason, signal.indicators, signal.news))
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
            elif age >= 300:
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
    return (f"Бумажная статистика MOEX 5m\n\nЗакрыто: {s['total']}/500\n"
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


async def send_signal(chat_id: str, signal: Signal, context: ContextTypes.DEFAULT_TYPE) -> None:
    text = (f"MOEX 5M — BUY-кандидат\n\nТикер: {signal.ticker}\nЦена входа: {signal.entry:.4f} ₽\n"
            f"Цель: {signal.target:.4f} ₽\nСтоп: {signal.stop:.4f} ₽\nСрок: 5 минут\n"
            f"Оценка условий: {signal.score:.1f}\nПричины: {signal.reason}\n"
            f"Индикаторы: {signal.indicators}\n{signal.news}\n\n"
            "Статус: бумажный сигнал, не приказ к покупке")
    await context.bot.send_message(chat_id=chat_id, text=text)


async def scan_once(context: ContextTypes.DEFAULT_TYPE) -> None:
    if not ADMIN_CHAT_ID:
        log.warning("ADMIN_CHAT_ID не задан: сканирование работает, но уведомлять некого")
    async with httpx.AsyncClient(timeout=15, headers={"User-Agent": "MOEX-Paper-Signal-Bot/1.0"}) as client:
        await update_open_trades(client)
        for ticker in TICKERS:
            try:
                conn = db(); already_open = active_trade(conn, ticker); conn.close()
                if already_open:
                    continue
                signal = await make_signal(client, ticker)
                if signal:
                    create_trade(signal)
                    if ADMIN_CHAT_ID:
                        await send_signal(ADMIN_CHAT_ID, signal, context)
                    log.info("paper signal %s %.4f", ticker, signal.entry)
            except (httpx.HTTPError, ValueError, KeyError, IndexError) as error:
                log.warning("scan %s: %s", ticker, error)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not authorized(update): return
    await update.message.reply_text("MOEX Paper Signal Bot активен. Используются только виртуальные сделки.\nКоманды: /scan /report /export /final_report")


async def scan_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not authorized(update): return
    await context.bot.send_chat_action(chat_id=update.effective_chat.id, action=ChatAction.TYPING)
    await scan_once(context)
    await update.message.reply_text("Сканирование завершено.\n\n" + stats_text())


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


async def background_scan(context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        await scan_once(context)
    except Exception:
        log.exception("background scan failed")


def main() -> None:
    if not TOKEN:
        raise RuntimeError("Не задана переменная TELEGRAM_BOT_TOKEN")
    db().close()
    application = Application.builder().token(TOKEN).build()
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("scan", scan_command))
    application.add_handler(CommandHandler("report", report))
    application.add_handler(CommandHandler("export", export_command))
    application.add_handler(CommandHandler("final_report", final_report))
    if application.job_queue:
        application.job_queue.run_repeating(background_scan, interval=SCAN_SECONDS, first=10)
    else:
        log.warning("JobQueue unavailable; install python-telegram-bot[job-queue]")
    application.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
