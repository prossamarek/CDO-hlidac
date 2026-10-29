#!/usr/bin/env python3
"""Hlídač termínů CDO.

Stáhne kalendář soutěží z dcs.czechdance.org, vyfiltruje to, co se vás týká,
pošle souhrn na WhatsApp (CallMeBot) a vygeneruje přehledný web (docs/index.html)
a kalendář pro import do Google/Apple kalendáře (docs/cdo.ics).

Použití:
    python main.py                  # normální běh
    python main.py --dry-run        # nic neposílá, jen vypíše zprávu
    python main.py --debug          # uloží do debug/ HTML, JSON a screenshot stránky
    python main.py --html soubor    # místo stahování zpracuje uloženou stránku
    python main.py --test-whatsapp  # pošle zkušební zprávu
"""
from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import re
import sys
import time
import unicodedata
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import urljoin
from zoneinfo import ZoneInfo

import requests
from bs4 import BeautifulSoup

log = logging.getLogger("cdo")

# --------------------------------------------------------------------------- #
# NASTAVENÍ – tady se upravuje, co vás zajímá
# --------------------------------------------------------------------------- #
CALENDAR_URL = os.getenv("CDO_CALENDAR_URL", "https://dcs.czechdance.org/calendar")

# Kolik dní před termínem se má poslat upozornění (0 = v den termínu).
REMIND_DAYS = [int(x) for x in os.getenv("REMIND_DAYS", "14,7,3,1,0").split(",") if x.strip()]
# V souhrnu se navíc ukážou všechny termíny v následujících N dnech.
SUMMARY_WINDOW_DAYS = 14
# Maximum detailních stránek soutěží, které se projdou při jednom běhu.
MAX_DETAIL_PAGES = 120

# Vaše disciplíny (regulární výrazy; (?-i:...) = rozlišuje velikost písmen).
DISCIPLINES = {
    "HH": [r"(?-i:\bHH\b)", r"hip[\s-]?hop", r"street\s?dance"],
    "DD": [r"(?-i:\bDD\b)", r"disco"],
    "ART": [r"(?-i:\bART\b)", r"art\s?dance", r"contemporary", r"současný tanec"],
}
# Soutěž bez rozpoznané disciplíny: True = přesto ji zahrnout (víc šumu, míň zmeškaných).
INCLUDE_UNKNOWN_DISCIPLINE = False

# Druhy akcí, které se týkají vás vždy (podle názvu).
KIND_PATTERNS = [
    ("skoleni", r"školení\s+trenér|trenérsk\w*\s+školení|školení\s+pro\s+trenér"),
    ("mcr", r"\bMČR\b|mistrovství\s+(české\s+republiky|čr)\b"),
    ("mc", r"mistrovství\s+čech"),
]
# Morava (vyřazuje se). Hledá se v názvu, regionu a místě konání.
MORAVIA = (r"morav|olomou|zlín|brno|brně|ostrav|opava|přerov|prostějov|hodonín|břeclav|"
           r"znojmo|uherské|vsetín|karviná|frýdek|šumperk|jeseník|kroměříž|vyškov|blansko")
# Na jaře (leden–červen) jen tyto regiony (kromě Mistrovství Čech a MČR).
SPRING_REGIONS = r"královéhradeck|pardubick|hradec králové|pardubic"

# --------------------------------------------------------------------------- #
TZ = ZoneInfo("Europe/Prague")
ROOT = Path(__file__).resolve().parent
DOCS = ROOT / "docs"
DEBUG_DIR = ROOT / "debug"
STATE_FILE = ROOT / "data" / "state.json"
UA = ("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/124.0 Safari/537.36 cdo-deadline-watcher/1.0")

DATE_FIELDS = ("event_date", "reg_open", "reg_close", "presence_close")
TYPE_LABELS = {
    "event_date": "Konání",
    "reg_open": "Otevření registrace",
    "reg_close": "Uzavření registrace",
    "presence_close": "Uzavření prezence",
}
WEEKDAYS = ["po", "út", "st", "čt", "pá", "so", "ne"]


# --------------------------------------------------------------------------- #
# Datový model
# --------------------------------------------------------------------------- #
@dataclass
class Event:
    id: str
    title: str
    url: str = ""
    event_date: str | None = None       # "YYYY-MM-DD" nebo "YYYY-MM-DDTHH:MM"
    reg_open: str | None = None
    reg_close: str | None = None
    presence_close: str | None = None
    region: str = ""
    place: str = ""
    info: str = ""
    kind: str = "soutez"
    disciplines: list[str] = field(default_factory=list)


# --------------------------------------------------------------------------- #
# Pomocné funkce: text a data
# --------------------------------------------------------------------------- #
def fold(s: str) -> str:
    """Malá písmena bez diakritiky."""
    s = unicodedata.normalize("NFKD", str(s))
    return "".join(c for c in s if not unicodedata.combining(c)).lower()


def clean(s) -> str:
    return re.sub(r"\s+", " ", str(s or "")).strip()


MONTHS = {"ledna": 1, "unora": 2, "brezna": 3, "dubna": 4, "kvetna": 5, "cervna": 6,
          "cervence": 7, "srpna": 8, "zari": 9, "rijna": 10, "listopadu": 11, "prosince": 12}
_RANGE = re.compile(r"(\d{1,2})\.\s*(?:(\d{1,2})\.\s*)?[–—-]\s*(\d{1,2})\.\s*(\d{1,2})\.\s*(\d{4})")
_NUM = re.compile(r"(\d{1,2})\.\s*(\d{1,2})\.\s*(\d{4})")
_ISO = re.compile(r"(\d{4})-(\d{2})-(\d{2})")
_NAMED = re.compile(r"(\d{1,2})\.?\s*(" + "|".join(MONTHS) + r")\s*(\d{4})")
_TIME = re.compile(r"\s*(?:,|v|ve|od|do)?\s*[T ]?\s*(\d{1,2}):(\d{2})")


def parse_dt(value) -> str | None:
    """Převede český/ISO zápis data (i s časem) na 'YYYY-MM-DD[THH:MM]'."""
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        if value > 1e11:           # milisekundy
            value /= 1000
        if value > 1e8:
            dt = datetime.fromtimestamp(value, TZ)
            return dt.strftime("%Y-%m-%dT%H:%M") if (dt.hour or dt.minute) else dt.strftime("%Y-%m-%d")
        return None
    t = fold(value)
    y = mo = d = None
    end = 0
    m = _RANGE.search(t)
    if m:   # "12.–13. 3. 2026" nebo "12. 3. – 13. 3. 2026" -> začátek
        d, mo, y, end = int(m[1]), int(m[2] or m[4]), int(m[5]), m.end()
    else:
        for rx, order in ((_ISO, "ymd"), (_NUM, "dmy"), (_NAMED, "dmn")):
            m = rx.search(t)
            if m:
                if order == "ymd":
                    y, mo, d = int(m[1]), int(m[2]), int(m[3])
                elif order == "dmy":
                    d, mo, y = int(m[1]), int(m[2]), int(m[3])
                else:
                    d, mo, y = int(m[1]), MONTHS[m[2]], int(m[3])
                end = m.end()
                break
    if y is None:
        return None
    try:
        date(y, mo, d)
    except ValueError:
        return None
    out = f"{y:04d}-{mo:02d}-{d:02d}"
    tm = _TIME.match(t[end:])
    if tm and int(tm[1]) < 24 and int(tm[2]) < 60 and (int(tm[1]) or int(tm[2])):
        out += f"T{int(tm[1]):02d}:{tm[2]}"
    return out


def days_left(iso: str, today: date) -> int:
    return (date.fromisoformat(iso[:10]) - today).days


def fmt_cs(iso: str | None, weekday: bool = True) -> str:
    if not iso:
        return "—"
    d = date.fromisoformat(iso[:10])
    s = f"{d.day}. {d.month}. {d.year}"
    if weekday:
        s = f"{WEEKDAYS[d.weekday()]} {s}"
    if len(iso) > 10:
        s += f" {iso[11:16]}"
    return s


# --------------------------------------------------------------------------- #
# Mapování popisků ("Uzavření registrace") na pole
# --------------------------------------------------------------------------- #
LABELS = [
    ("reg_open", ["otevreni registrace", "zahajeni registrace", "otevreni prihlasovani",
                  "zahajeni prihlasovani", "registrace od", "prihlasky od",
                  "registration open", "registration start", "reg open"]),
    ("reg_close", ["uzavreni registrace", "ukonceni registrace", "uzaverka registrace",
                   "uzavreni prihlasovani", "ukonceni prihlasovani", "uzaverka prihlasek",
                   "uzavreni prihlasek", "registrace do", "prihlasky do",
                   "registration close", "registration end", "reg close", "deadline"]),
    ("presence_close", ["uzavreni prezence", "ukonceni prezence", "uzaverka prezence",
                        "prezence do", "presence close", "presence end"]),
    ("region", ["region", "kraj", "oblast"]),
    ("place", ["misto", "mesto", "city", "place", "location", "venue"]),
    ("event_date", ["datum konani", "termin konani", "datum souteze", "konani", "datum",
                    "termin", "date", "start"]),
    ("title", ["nazev", "soutez", "akce", "name", "title", "summary"]),
]


def map_label(label: str) -> str | None:
    label = re.sub(r"([a-z])([A-Z])", r"\1 \2", str(label))   # camelCase -> slova
    l = re.sub(r"[^a-z0-9 ]+", " ", fold(label)).strip()
    padded = f" {l} "
    for field_name, aliases in LABELS:
        for a in aliases:
            if (a in l) if " " in a else (f" {a} " in padded):
                return field_name
    return None


def make_id(url: str, title: str) -> str:
    return hashlib.sha1((url or title).encode("utf-8")).hexdigest()[:10]


def make_event(m: dict, url: str = "", info: str = "") -> Event | None:
    title = clean(m.get("title"))
    if not title:
        return None
    return Event(
        id=make_id(url, title), title=title, url=url,
        event_date=parse_dt(m.get("event_date")), reg_open=parse_dt(m.get("reg_open")),
        reg_close=parse_dt(m.get("reg_close")), presence_close=parse_dt(m.get("presence_close")),
        region=clean(m.get("region"))[:120], place=clean(m.get("place"))[:120],
        info=clean(info)[:2000],
    )


# --------------------------------------------------------------------------- #
# Parsování: JSON z pozadí stránky a HTML tabulky
# --------------------------------------------------------------------------- #
def _record_lists(obj):
    if isinstance(obj, list):
        if obj and all(isinstance(x, dict) for x in obj[:5]):
            yield obj
        for x in obj:
            yield from _record_lists(x)
    elif isinstance(obj, dict):
        for v in obj.values():
            yield from _record_lists(v)


def events_from_json(payloads: list[dict], base_url: str) -> list[Event]:
    out = []
    for p in payloads:
        for records in _record_lists(p.get("data")):
            for rec in records:
                mapped = {}
                for k, v in rec.items():
                    if isinstance(v, (str, int, float)) and not isinstance(v, bool):
                        f = map_label(k)
                        if f and f not in mapped:
                            mapped[f] = v
                if not (mapped.get("title") and mapped.get("event_date")):
                    continue
                link = next((rec[k] for k in ("url", "link", "href", "detailUrl") if rec.get(k)), "")
                ev = make_event(mapped, urljoin(base_url, str(link)) if link else "",
                                " ".join(f"{k}: {v}" for k, v in rec.items()
                                         if isinstance(v, (str, int, float))))
                if ev and ev.event_date:
                    out.append(ev)
    return out


def events_from_html(html: str, base_url: str) -> list[Event]:
    soup = BeautifulSoup(html, "lxml")
    out = []
    for table in soup.find_all("table"):
        header = next((tr for tr in table.find_all("tr") if tr.find("th")), None)
        if header is None:
            continue
        cols = [map_label(th.get_text(" ", strip=True)) for th in header.find_all("th")]
        if "title" not in cols and "event_date" not in cols:
            continue
        for tr in table.find_all("tr"):
            cells = tr.find_all("td")
            if not cells:
                continue
            mapped = {}
            for f, td in zip(cols, cells):
                if f and f not in mapped:
                    mapped[f] = td.get_text(" ", strip=True)
            a = tr.find("a", href=True)
            ev = make_event(mapped, urljoin(base_url, a["href"]) if a else "",
                            tr.get_text(" ", strip=True))
            if ev and ev.event_date:
                out.append(ev)
    return out


def detail_pairs(html: str) -> list[tuple[str, str]]:
    """Dvojice 'popisek: hodnota' z detailu soutěže (dl, tabulka, řádky 'X: Y')."""
    soup = BeautifulSoup(html, "lxml")
    pairs: list[tuple[str, str]] = []
    for dt in soup.find_all("dt"):
        dd = dt.find_next_sibling("dd")
        if dd:
            pairs.append((dt.get_text(" ", strip=True), dd.get_text(" ", strip=True)))
    for tr in soup.find_all("tr"):
        cells = tr.find_all(["th", "td"])
        if len(cells) == 2:
            pairs.append((cells[0].get_text(" ", strip=True), cells[1].get_text(" ", strip=True)))
    for el in soup.find_all(["p", "li", "div", "span"]):
        txt = el.get_text(" ", strip=True)
        if 3 < len(txt) < 200 and ":" in txt and not el.find(["p", "li", "div"]):
            label, _, val = txt.partition(":")
            pairs.append((label.strip(), val.strip()))
    return [(l, v) for l, v in pairs if l and v]


def apply_pairs(ev: Event, pairs: list[tuple[str, str]]) -> None:
    for label, val in pairs:
        f = map_label(label)
        if f in ("reg_open", "reg_close", "presence_close"):
            parsed = parse_dt(val)
            if parsed:
                setattr(ev, f, parsed)          # detail je přesnější než seznam
        elif f == "event_date" and not ev.event_date:
            ev.event_date = parse_dt(val)
        elif f in ("region", "place") and not getattr(ev, f):
            setattr(ev, f, clean(val)[:120])
    ev.info = clean(ev.info + " " + " ".join(f"{l}: {v}" for l, v in pairs))[:2000]


# --------------------------------------------------------------------------- #
# Stahování (Playwright = skutečný prohlížeč, zvládne JavaScript)
# --------------------------------------------------------------------------- #
def dump_debug(html: str, payloads: list[dict], page=None) -> None:
    DEBUG_DIR.mkdir(exist_ok=True)
    (DEBUG_DIR / "page.html").write_text(html, encoding="utf-8")
    (DEBUG_DIR / "json_responses.json").write_text(
        json.dumps(payloads, ensure_ascii=False, indent=1)[:3_000_000], encoding="utf-8")
    if page is not None:
        try:
            page.screenshot(path=str(DEBUG_DIR / "screenshot.png"), full_page=True)
        except Exception as exc:  # noqa: BLE001
            log.warning("Screenshot se nepovedl: %s", exc)
    log.info("Ladicí soubory uloženy do %s", DEBUG_DIR)


def scrape(url: str, debug: bool) -> list[Event]:
    from playwright.sync_api import sync_playwright   # import až tady, ať jde zbytek testovat bez něj

    payloads: list[dict] = []

    def on_response(resp):
        try:
            if "json" in (resp.headers.get("content-type") or ""):
                payloads.append({"url": resp.url, "data": resp.json()})
        except Exception:  # noqa: BLE001
            pass

    with sync_playwright() as pw:
        browser = pw.chromium.launch()
        ctx = browser.new_context(locale="cs-CZ", timezone_id="Europe/Prague", user_agent=UA,
                                  viewport={"width": 1400, "height": 2000})
        page = ctx.new_page()
        page.on("response", on_response)
        log.info("Otevírám %s", url)
        resp = page.goto(url, wait_until="domcontentloaded", timeout=60_000)
        log.info("HTTP stav: %s", resp.status if resp else "?")
        try:
            page.wait_for_load_state("networkidle", timeout=30_000)
        except Exception:  # noqa: BLE001
            log.warning("Stránka se do 30 s úplně neuklidnila, pokračuji s tím, co je.")
        page.wait_for_timeout(1500)
        html = page.content()

        by_json = events_from_json(payloads, url)
        by_html = events_from_html(html, url)
        events = by_json if len(by_json) > len(by_html) else by_html
        log.info("Nalezeno v JSON: %d, v HTML tabulkách: %d", len(by_json), len(by_html))
        if debug or not events:
            dump_debug(html, payloads, page)

        today = datetime.now(TZ).date()
        todo = [e for e in events if e.url and (e.event_date or "9999")[:10] >= today.isoformat()
                and not (e.reg_open and e.reg_close and e.presence_close)]
        todo.sort(key=lambda e: e.event_date or "")
        log.info("Detailní stránky ke stažení: %d", min(len(todo), MAX_DETAIL_PAGES))
        for ev in todo[:MAX_DETAIL_PAGES]:
            try:
                page.goto(ev.url, wait_until="domcontentloaded", timeout=45_000)
                try:
                    page.wait_for_load_state("networkidle", timeout=10_000)
                except Exception:  # noqa: BLE001
                    pass
                apply_pairs(ev, detail_pairs(page.content()))
                time.sleep(0.5)
            except Exception as exc:  # noqa: BLE001
                log.warning("Detail %s selhal: %s", ev.url, exc)
        browser.close()
    return events


# --------------------------------------------------------------------------- #
# Filtr: co se vás týká
# --------------------------------------------------------------------------- #
def classify(ev: Event) -> None:
    ev.kind = "soutez"
    for kind, pat in KIND_PATTERNS:
        if re.search(pat, ev.title, re.I):
            ev.kind = kind
            break
    blob = f"{ev.title} {ev.info}"
    ev.disciplines = [d for d, pats in DISCIPLINES.items()
                      if any(re.search(p, blob, re.I) for p in pats)]


def is_relevant(ev: Event) -> tuple[bool, str]:
    if ev.kind == "skoleni":
        return True, "školení trenérů"
    if not ev.disciplines and not INCLUDE_UNKNOWN_DISCIPLINE:
        return False, "jiná/nerozpoznaná disciplína"
    if ev.kind in ("mcr", "mc"):
        return True, "mistrovství"
    geo = f"{ev.title} {ev.region} {ev.place}"
    if re.search(MORAVIA, geo, re.I):
        return False, "Morava"
    month = int((ev.event_date or "2000-09")[5:7])
    if month <= 6 and not re.search(SPRING_REGIONS, geo, re.I):
        return False, "jaro: jiný region než KHK/PCE"
    return True, "soutěž v Čechách"


def filter_events(events: list[Event], today: date) -> list[Event]:
    seen_ids: dict[str, Event] = {}
    for ev in events:                        # deduplikace
        if ev.id in seen_ids and seen_ids[ev.id].event_date != ev.event_date:
            ev.id = make_id(ev.url, f"{ev.title}{ev.event_date}")
        seen_ids.setdefault(ev.id, ev)
    kept = []
    for ev in seen_ids.values():
        classify(ev)
        last = max((getattr(ev, f) for f in DATE_FIELDS if getattr(ev, f)), default=None)
        if last is None or last[:10] < today.isoformat():
            continue                         # proběhlo
        ok, why = is_relevant(ev)
        log.info("%s %-60s -> %s", "✔" if ok else "✘", ev.title[:60], why)
        if ok:
            kept.append(ev)
    kept.sort(key=lambda e: e.event_date or e.reg_close or "9999")
    return kept


# --------------------------------------------------------------------------- #
# Stav (aby se upozornění neposílala dvakrát) a zpráva
# --------------------------------------------------------------------------- #
def load_state() -> dict:
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return {"seen": {}, "sent": {}}


def save_state(state: dict) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8")


def when_text(n: int) -> str:
    return "DNES" if n == 0 else "zítra" if n == 1 else f"za {n} {'dny' if n < 5 else 'dní'}"


ICON = {"reg_open": "🟢 otevření registrace", "reg_close": "🔴 uzavření registrace",
        "presence_close": "🟠 uzavření prezence"}


def build_message(events: list[Event], state: dict, today: date, dashboard_url: str):
    """Vrátí (text|None, klíče odeslaných upozornění, nový stav 'seen')."""
    first_run = not state.get("seen")
    sent = state.get("sent", {})
    new_keys: dict[str, str] = {}
    due: list[tuple[int, str, Event, str]] = []
    for ev in events:
        for f in ("reg_open", "reg_close", "presence_close"):
            iso = getattr(ev, f)
            if not iso:
                continue
            n = days_left(iso, today)
            key = f"{ev.id}:{f}:{n}:{iso}"
            if n in REMIND_DAYS and key not in sent:
                due.append((n, f, ev, iso))
                new_keys[key] = iso[:10]
    seen_now = {ev.id: {f: getattr(ev, f) for f in DATE_FIELDS} for ev in events}

    news, changes = [], []
    if not first_run:
        for ev in events:
            prev = state["seen"].get(ev.id)
            if prev is None:
                news.append(f"• {ev.title} – {fmt_cs(ev.event_date, False)}")
                continue
            for f in DATE_FIELDS:
                new, old = getattr(ev, f), prev.get(f)
                if new and old != new:
                    what = f"{fmt_cs(old, False)} → {fmt_cs(new, False)}" if old else f"nově {fmt_cs(new, False)}"
                    changes.append(f"• {ev.title}: {TYPE_LABELS[f].lower()} {what}")

    if not (due or news or changes):
        return None, new_keys, seen_now

    lines = [f"*CDO – hlídač termínů* ({fmt_cs(today.isoformat())})"]
    if due:
        lines.append("")
        for n, f, ev, iso in sorted(due, key=lambda x: (x[0], x[3])):
            disc = f" [{', '.join(ev.disciplines)}]" if ev.disciplines else ""
            lines.append(f"⏰ *{when_text(n)}* – {ICON[f]}\n   {ev.title}{disc}\n   {fmt_cs(iso)}")
    due_ids = {(ev.id, f) for _, f, ev, _ in due}
    later = []
    for ev in events:
        for f in ("reg_close", "presence_close"):
            iso = getattr(ev, f)
            if iso and (ev.id, f) not in due_ids and 0 <= days_left(iso, today) <= SUMMARY_WINDOW_DAYS:
                later.append((iso, f, ev))
    if later:
        lines += ["", f"📅 *Dále v příštích {SUMMARY_WINDOW_DAYS} dnech*"]
        lines += [f"• {fmt_cs(iso, False)} {ICON[f].split(' ', 1)[1]} – {ev.title}" for iso, f, ev in sorted(later)]
    if news:
        lines += ["", "🆕 *Nové v kalendáři*"] + news
    if changes:
        lines += ["", "✏️ *Změny termínů*"] + changes
    if dashboard_url:
        lines += ["", f"🔗 {dashboard_url}"]
    return "\n".join(lines), new_keys, seen_now


# --------------------------------------------------------------------------- #
# WhatsApp přes CallMeBot
# --------------------------------------------------------------------------- #
def chunk_text(text: str, limit: int = 1200) -> list[str]:
    chunks, cur = [], ""
    for line in text.split("\n"):
        if cur and len(cur) + len(line) + 1 > limit:
            chunks.append(cur)
            cur = ""
        cur = f"{cur}\n{line}" if cur else line
    return chunks + ([cur] if cur else [])


def whatsapp_configured() -> bool:
    return bool(os.getenv("WHATSAPP_PHONE", "").strip() and os.getenv("WHATSAPP_APIKEY", "").strip())


def send_whatsapp(text: str, dry_run: bool) -> bool:
    phones = [p.strip() for p in os.getenv("WHATSAPP_PHONE", "").split(",") if p.strip()]
    keys = [k.strip() for k in os.getenv("WHATSAPP_APIKEY", "").split(",") if k.strip()]
    if dry_run or not phones:
        log.info("%s\n--- zpráva ---\n%s\n--------------",
                 "DRY-RUN" if dry_run else "WhatsApp není nastaven (chybí secrets) – zprávu neposílám", text)
        return dry_run
    if len(phones) != len(keys):
        log.error("Počet čísel a API klíčů v secrets se liší.")
        return False
    ok = True
    for phone, key in zip(phones, keys):
        for part in chunk_text(text):
            try:
                r = requests.get("https://api.callmebot.com/whatsapp.php",
                                 params={"phone": phone, "text": part, "apikey": key}, timeout=30)
                if r.status_code != 200 or "error" in r.text.lower():
                    log.error("CallMeBot odmítl zprávu (%s): %s", r.status_code, r.text[:200])
                    ok = False
                else:
                    log.info("Zpráva odeslána na ***%s", phone[-3:])
            except requests.RequestException as exc:
                log.error("Odeslání selhalo: %s", exc)
                ok = False
            time.sleep(5)
    return ok


# --------------------------------------------------------------------------- #
# Výstupy: events.json, index.html, cdo.ics
# --------------------------------------------------------------------------- #
def ics_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace(";", "\\;").replace(",", "\\,").replace("\n", "\\n")


def ics_fold(line: str) -> str:
    out, cur, size = [], "", 0
    for ch in line:
        b = len(ch.encode("utf-8"))
        if size + b > 74:
            out.append(cur)
            cur, size = " ", 1
        cur += ch
        size += b
    out.append(cur)
    return "\r\n".join(out)


def build_ics(events: list[Event]) -> str:
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    L = ["BEGIN:VCALENDAR", "VERSION:2.0", "PRODID:-//CDO hlidac terminu//CS", "CALSCALE:GREGORIAN",
         "X-WR-CALNAME:CDO termíny", "X-WR-TIMEZONE:Europe/Prague"]
    for ev in events:
        for f in DATE_FIELDS:
            iso = getattr(ev, f)
            if not iso:
                continue
            L += ["BEGIN:VEVENT", f"UID:{ev.id}-{f}@cdo-hlidac", f"DTSTAMP:{stamp}",
                  f"SUMMARY:{ics_escape(f'[{TYPE_LABELS[f]}] {ev.title}')}"]
            if len(iso) > 10:
                start = datetime.fromisoformat(iso).replace(tzinfo=TZ).astimezone(timezone.utc)
                L += [f"DTSTART:{start:%Y%m%dT%H%M%SZ}",
                      f"DTEND:{start + timedelta(minutes=30):%Y%m%dT%H%M%SZ}"]
            else:
                d = date.fromisoformat(iso)
                L += [f"DTSTART;VALUE=DATE:{d:%Y%m%d}", f"DTEND;VALUE=DATE:{d + timedelta(days=1):%Y%m%d}"]
            desc = "\n".join(x for x in (", ".join(ev.disciplines), ev.place or ev.region, ev.url) if x)
            if desc:
                L.append(f"DESCRIPTION:{ics_escape(desc)}")
            if f in ("reg_close", "presence_close"):
                L += ["BEGIN:VALARM", "ACTION:DISPLAY", f"DESCRIPTION:{ics_escape(TYPE_LABELS[f])}",
                      "TRIGGER:-P1D", "END:VALARM"]
            L.append("END:VEVENT")
    L.append("END:VCALENDAR")
    return "\r\n".join(ics_fold(x) for x in L) + "\r\n"


def write_outputs(events: list[Event], now: datetime) -> None:
    DOCS.mkdir(exist_ok=True)
    payload = {"generated_at": now.strftime("%-d. %-m. %Y %H:%M"),
               "calendar_url": CALENDAR_URL, "events": [asdict(e) for e in events]}
    (DOCS / "events.json").write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    template = (ROOT / "template.html").read_text(encoding="utf-8")
    data = json.dumps(payload, ensure_ascii=False).replace("</", "<\\/")
    (DOCS / "index.html").write_text(template.replace("__DATA__", data), encoding="utf-8")
    (DOCS / "cdo.ics").write_text(build_ics(events), encoding="utf-8", newline="")
    log.info("Výstupy zapsány do %s (%d soutěží)", DOCS, len(events))


# --------------------------------------------------------------------------- #
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true", help="neposílat WhatsApp")
    ap.add_argument("--debug", action="store_true", help="uložit ladicí soubory do debug/")
    ap.add_argument("--html", help="zpracovat uložený HTML soubor místo stahování")
    ap.add_argument("--test-whatsapp", action="store_true", help="poslat zkušební zprávu a skončit")
    args = ap.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s", stream=sys.stdout)

    if args.test_whatsapp:
        return 0 if send_whatsapp("✅ Hlídač termínů CDO funguje. Tuhle zprávu jste si právě vyžádali.",
                                  args.dry_run) else 1

    now = datetime.now(TZ)
    today = now.date()
    repo = os.getenv("GITHUB_REPOSITORY", "")
    dashboard_url = os.getenv("DASHBOARD_URL") or (
        f"https://{repo.split('/')[0]}.github.io/{repo.split('/')[1]}/" if "/" in repo else "")

    try:
        if args.html:
            html = Path(args.html).read_text(encoding="utf-8")
            events = events_from_html(html, CALENDAR_URL)
        else:
            events = scrape(CALENDAR_URL, args.debug)
    except Exception:  # noqa: BLE001
        log.exception("Stažení kalendáře selhalo")
        return 1
    if not events:
        log.error("Nenalezena žádná soutěž – stránka se nejspíš změnila nebo se nenačetla. "
                  "Předchozí data zůstávají beze změny. Zkontrolujte artefakt 'debug'.")
        return 1

    kept = filter_events(events, today)
    log.info("Celkem %d akcí, po filtru %d.", len(events), len(kept))

    state = load_state()
    message, new_keys, seen_now = build_message(kept, state, today, dashboard_url)
    ok, delivered = True, True
    if message:
        if args.dry_run or whatsapp_configured():
            ok = delivered = send_whatsapp(message, args.dry_run)
        else:
            log.warning("WhatsApp není nastaven, upozornění nebylo odesláno (web se přesto aktualizuje).")
            delivered = False

    write_outputs(kept, now)
    if not args.dry_run:
        state["last_run"] = now.isoformat(timespec="seconds")   # denní změna = repozitář zůstává "aktivní"
        if ok and delivered:
            cutoff = (today - timedelta(days=30)).isoformat()
            state["sent"] = {k: v for k, v in {**state.get("sent", {}), **new_keys}.items() if v >= cutoff}
            state["seen"] = seen_now
        save_state(state)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
