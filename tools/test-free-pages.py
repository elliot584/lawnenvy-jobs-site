#!/usr/bin/env python3
"""Browser tests for the free tool pages (/free, /free/gst-calculator, /free/cents-per-km-calculator,
/free/bas-due-dates, /free/hourly-rate-calculator, /free/quote-template).

Run it with the app repo's Python, which has Playwright and a cached headless Chromium
(there is no Node on this machine):

  PY="/Users/elliotlangham/Documents/Lawn envy revamp/jobs-app/tools/demo-capture/.venv/bin/python"
  "$PY" tools/test-free-pages.py                       # the whole suite; PASS/FAIL per check, exit 1 on any FAIL
  "$PY" tools/test-free-pages.py --selftest            # breaks the pages on purpose, ~45 ways, and checks the suite goes red each time
  "$PY" tools/test-free-pages.py --only gst,bas        # just those groups (while developing)
  "$PY" tools/test-free-pages.py --page quote-template # just one page
  "$PY" tools/test-free-pages.py --browser webkit      # the same suite in WebKit (Safari's engine); the PDF check is Chromium-only
  "$PY" tools/test-free-pages.py --shots DIR           # also saves a screenshot of every page at 375 and 1280 px, light and dark

Groups: static, gst, km, bas, hourly, quote, print, net, layout, a11y, cta.

How it works: the site folder is served from a local threaded http.server that answers clean URLs the way
Vercel does (/free/gst-calculator -> free/gst-calculator.html). Every request to anywhere else is aborted and
recorded, and window.fbq is stubbed before any page script runs so Meta's snippet does nothing. The
calculators are checked against a second, independent implementation of the sums in Python (decimal
arithmetic with ROUND_HALF_UP), the BAS dates against a Python calendar, with the browser clock set
(page.clock) and a browser time zone chosen per case. Nothing waits on a fixed sleep. Python 3.9 compatible.

The numbers the pages may state come from FACTS.md (marketing-kit/social-bank/FACTS.md in the app repo's
parent folder); the constants below are copies of the ones this suite checks, with their ids.

Every 1 July (and whenever the ATO changes a page): re-read the ATO pages listed in ATO below, then change the
rates (KM_RATES), the due dates (BAS_QUARTERLY and the months in BAS_MONTHLY), the "page updated" dates and
the "Checked against the ATO pages on" date here AND in the pages. The suite fails until both agree, which is
the point. After the last 2026-27 date (28 July 2027) the BAS page says its dates have passed; add the next
year's table before then.
"""
import argparse
import http.server
import json
import random
import re
import shutil
import socketserver
import sys
import tempfile
import threading
from datetime import date, datetime, timedelta, timezone
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from urllib.parse import urlsplit

from playwright.sync_api import sync_playwright
from zoneinfo import ZoneInfo

SITE = Path(__file__).resolve().parent.parent
BASE_URL = "https://www.keptsoftware.com.au"
APP_FREE = "https://app.keptsoftware.com.au/?industry=lawn_care"
APP_DEMO = "https://app.keptsoftware.com.au/?demo=1"
TAX_NOTE = ("Kept's tax tools are estimates to help with your reporting, not professional advice: "
            "check anything that matters with your accountant.")

SLUGS = ["gst-calculator", "cents-per-km-calculator", "bas-due-dates", "hourly-rate-calculator", "quote-template"]
PAGE_PATH = {"": "/free"}
for _s in SLUGS:
    PAGE_PATH[_s] = "/free/" + _s
ALL_PAGES = [""] + SLUGS

GROUPS = ["static", "gst", "km", "bas", "hourly", "quote", "print", "net", "layout", "a11y", "cta"]

# ---------------------------------------------------------------------------------------------
# What the pages must say (FACTS.md ids in the comments; ATO pages re-read on 24 October 2026)
# ---------------------------------------------------------------------------------------------
ATO = {
    "howgst": ("https://www.ato.gov.au/businesses-and-organisations/gst-excise-and-indirect-taxes/gst/how-gst-works", "14 September 2026"),
    "reggst": ("https://www.ato.gov.au/businesses-and-organisations/gst-excise-and-indirect-taxes/gst/registering-for-gst", "14 September 2026"),  # F-GST-1, F-GST-2
    "km": ("https://www.ato.gov.au/individuals-and-families/income-deductions-offsets-and-records/deductions-you-can-claim/work-related-deductions/cars-transport-and-travel/motor-vehicle-and-car-expenses/expenses-for-a-car-you-own-or-lease/cents-per-kilometre-method", "12 August 2026"),  # F-KM-1
    "bas": ("https://www.ato.gov.au/businesses-and-organisations/preparing-lodging-and-paying/business-activity-statements-bas/due-dates-for-lodging-and-paying-your-bas", "17 September 2026"),  # F-BAS-1..4
}
SOURCES = {
    "gst-calculator": ["howgst", "reggst"],
    "cents-per-km-calculator": ["km"],
    "bas-due-dates": ["bas"],
    "hourly-rate-calculator": ["howgst"],
    "quote-template": ["howgst"],
}
# F-KM-1: rate in cents per km by income year; maximum 5,000 km per car per year.
KM_RATES = {"2026-27": 91, "2025-26": 88, "2024-25": 88}
KM_MAX = Decimal(5000)
# F-BAS-1: quarterly due dates for 2026-27. F-BAS-2: monthly is the 21st of the month after the period.
BAS_QUARTERLY = [date(2026, 10, 28), date(2027, 2, 28), date(2027, 4, 28), date(2027, 7, 28)]
BAS_MONTHLY = []
for _y, _m in [(2026, 7), (2026, 8), (2026, 9), (2026, 10), (2026, 11), (2026, 12), (2027, 1), (2027, 2), (2027, 3), (2027, 4), (2027, 5), (2027, 6)]:
    BAS_MONTHLY.append(date(_y + (_m == 12), _m % 12 + 1, 21))
F_BAS_3 = ("If you lodge online you may be eligible for an extra 2 weeks to lodge and pay your quarterly BAS, "
           "and you may get extra time if you lodge through a registered tax or BAS agent. "
           "A later date does not apply to Quarter 2 because its due date already includes a one-month extension.")
F_BAS_2_WEEKEND = "you have until the next business day"
# Statements each page must contain (checked in the page's visible text).
MUST_SAY = {
    "gst-calculator": ["10%", "one-eleventh", "$220", "$200", "$20 GST", "nearest cent", "half a cent", "$75,000", "$150,000", "21 days", "12 months", "ABN"],
    "cents-per-km-calculator": ["91 cents", "88 cents", "2026-27", "2025-26", "2024-25", "5,000", "accountant", "receipts", "myDeductions", "decline in value", "registration", "insurance", "maintenance", "repairs", "fuel"],
    "bas-due-dates": ["28 October", "28 February", "28 April", "28 July", "21st day of the month", "$20 million", "$200,000", "31 October", "$75,000", "$150,000", "general interest charge", F_BAS_3, F_BAS_2_WEEKEND],
    "hourly-rate-calculator": ["estimate", "not tax advice", "billable"],
    "quote-template": ["Add GST (10%)", "Print or save as PDF", "A4"],
}
# Every dollar amount and percentage that may appear in a page's static text. Anything else is a stray number.
ALLOWED_AMOUNTS = {
    "": set(),
    "gst-calculator": {"$220", "$200", "$20", "$22", "$0.05", "$75,000", "$150,000"},
    "cents-per-km-calculator": {"$4,550.00", "$4,400.00"},
    "bas-due-dates": {"$20 million", "$200,000", "$75,000", "$150,000"},
    "hourly-rate-calculator": {"$80,000", "$20,000", "$100,000", "$86.96"},
    "quote-template": {"$0.00"},
}
ALLOWED_PERCENTS = {
    "": {"10%"},
    "gst-calculator": {"10%", "110%"},
    "cents-per-km-calculator": set(),
    "bas-due-dates": set(),
    "hourly-rate-calculator": {"10%"},
    "quote-template": {"10%"},
}
# Words the pages must not use (the "Do NOT say" list in APP-CLAIMS.md and the ads pack), as regexes.
HELD = [
    (r"pay now", "Pay now"), (r"payment links?", "payment links"), (r"tap to pay", "tap to pay"),
    (r"card payments?", "card payments"), (r"online payments?", "online payments"), (r"pay online", "pay online"),
    (r"\bautomatic", "automatic"), (r"autopilot", "autopilot"), (r"set[ -]and[ -]forget", "set and forget"),
    (r"messag\w* your (customers|clients)", "messaging customers"), (r"text(s|ing)? your (customers|clients)", "texting customers"),
    (r"route optimi", "route optimisation"),
    (r"tax invoice", "tax invoice"),
    (r"3 months free|three months free|months? free", "months free"), (r"free forever", "free forever"), (r"\btrial\b", "trial"),
    (r"\bfounding\b", "founding offer"),
    (r"encrypt", "encryption"), (r"bank[- ]grade", "bank-grade"), (r"\bsecur(e|ity)\b", "security"),
    (r"artificial intelligence|machine learning", "AI"),
    (r"marketplace", "Marketplace"),
    (r"testimonial", "testimonials"), (r"trusted by", "trusted by"), (r"thousands of", "thousands of"), (r"\busers\b", "users"),
    (r"\$\s?(35|69|119|229|21)\b", "a Kept price"), (r"\b(solo|crew|team|operation) plan\b", "a plan name"), (r"/ ?mo\b|per month", "a monthly price"),
    (r"\bbest\b", "best"), (r"#1\b|number one", "#1"),
    (r"ato[- ]approved|endorsed by the ato", "ATO endorsement"),
]
HELD_CASE_SENSITIVE = [(r"\bAI\b", "AI")]

EXTERNAL_OK = {"www.keptsoftware.com.au", "app.keptsoftware.com.au", "www.ato.gov.au", "www.lawnenvyaustralia.com", "schema.org",
                "connect.facebook.net", "www.facebook.com"}

D = Decimal


# ---------------------------------------------------------------------------------------------
# The independent oracle: the sums done in decimal arithmetic
# ---------------------------------------------------------------------------------------------
def q2(x):
    return D(x).quantize(D("0.01"), rounding=ROUND_HALF_UP)


def money(x):
    return "${:,.2f}".format(q2(x))


def gst_add(price):
    price = q2(price)
    gst = q2(price * D("0.1"))
    return price, gst, price + gst          # before, gst, total


def gst_remove(total):
    total = q2(total)
    gst = q2(total / D(11))
    return total - gst, gst, total          # before, gst, total


def effective(d):
    """A weekend due date moves to the Monday."""
    return d + timedelta(days=(7 - d.weekday()) if d.weekday() >= 5 else 0)


DAYNAMES = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
MONTHNAMES = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"]


def nice(d):
    return "%s %d %s %d" % (DAYNAMES[d.weekday()], d.day, MONTHNAMES[d.month - 1], d.year)


def next_due(dates, today):
    for d in dates:
        e = effective(d)
        if e >= today:
            return e
    return None


def when_phrase(days):
    return "due today" if days == 0 else ("due tomorrow" if days == 1 else "due in %d days" % days)


# ---------------------------------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------------------------------
class Results:
    def __init__(self, echo=True):
        self.rows = []
        self.echo = echo

    def section(self, name):
        if self.echo:
            print("\n== %s" % name, flush=True)

    def check(self, group, name, ok, detail=""):
        ok = bool(ok)
        self.rows.append((group, name, ok, detail))
        if self.echo:
            line = "%s  [%s] %s" % ("PASS" if ok else "FAIL", group, name)
            if not ok and detail != "":
                line += "\n        -> %s" % (str(detail)[:600],)
            print(line, flush=True)

    @property
    def failed(self):
        return [r for r in self.rows if not r[2]]


# ---------------------------------------------------------------------------------------------
# A local server for a site folder, with clean URLs like Vercel's
# ---------------------------------------------------------------------------------------------
class Handler(http.server.SimpleHTTPRequestHandler):
    extensions_map = dict(http.server.SimpleHTTPRequestHandler.extensions_map)
    extensions_map.update({".woff2": "font/woff2", ".js": "text/javascript", ".svg": "image/svg+xml"})

    def translate_path(self, path):
        path = path.split("?", 1)[0].split("#", 1)[0]
        rel = path.lstrip("/")
        root = Path(self.directory)
        p = root / rel
        if p.is_dir():
            return str(p / "index.html")
        if not p.exists() and (root / (rel + ".html")).exists():
            return str(root / (rel + ".html"))
        return str(p)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def log_message(self, *a):
        pass


class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True


class Site:
    def __init__(self, root):
        self.root = Path(root)
        handler = lambda *a, **kw: Handler(*a, directory=str(self.root), **kw)   # noqa: E731
        self.srv = Server(("127.0.0.1", 0), handler)
        self.base = "http://127.0.0.1:%d" % self.srv.server_address[1]
        threading.Thread(target=self.srv.serve_forever, daemon=True).start()

    def close(self):
        self.srv.shutdown()
        self.srv.server_close()


# Injected before any page script: Meta's snippet sees window.fbq and does nothing; print, fetch, XHR and
# sendBeacon are counted so a leak shows up even when it fails.
INIT_STUB = r"""
(function () {
  window.fbq = function () { (window.__fbq = window.__fbq || []).push([].slice.call(arguments)); };
  window.__printed = 0;
  window.print = function () { window.__printed++; };
  window.__beacons = []; window.__fetch = 0; window.__xhr = 0; window.__ws = 0;
  try { navigator.sendBeacon = function () { window.__beacons.push([].slice.call(arguments)); return true; }; } catch (e) {}
  var f = window.fetch; window.fetch = function () { window.__fetch++; return f.apply(this, arguments); };
  var o = XMLHttpRequest.prototype.open; XMLHttpRequest.prototype.open = function () { window.__xhr++; return o.apply(this, arguments); };
  var W = window.WebSocket; if (W) { window.WebSocket = function () { window.__ws++; return new W(arguments[0], arguments[1]); }; }
})();
"""


class Env:
    """Browser + site, with helpers to open a page in a fresh context."""

    def __init__(self, browser, site, browser_name="chromium"):
        self.browser = browser
        self.site = site
        self.base = site.base
        self.root = site.root
        self.browser_name = browser_name

    def session(self, scheme="light", width=1280, height=900, tz="Australia/Brisbane", clock=None, stub=True,
                storage_init=None, fbevents=False):
        return Session(self, scheme, width, height, tz, clock, stub, storage_init, fbevents)

    def read(self, rel):
        return (self.root / rel).read_text(encoding="utf-8")

    def page_file(self, slug):
        return "free/index.html" if slug == "" else "free/%s.html" % slug


class Session:
    def __init__(self, env, scheme, width, height, tz, clock, stub, storage_init, fbevents):
        self.env = env
        self.requests = []          # (url, method, resource_type, post_data)
        self.blocked = []           # off-site URLs that were aborted
        self.errors = []            # uncaught page errors and console errors
        self.ctx = env.browser.new_context(viewport={"width": width, "height": height}, color_scheme=scheme,
                                           timezone_id=tz, locale="en-AU")
        if stub:
            self.ctx.add_init_script(INIT_STUB)
        else:
            # Let Meta's own snippet run, but serve it an empty script, and only count what it asks for.
            self.ctx.add_init_script(INIT_STUB.replace("window.fbq = function () { (window.__fbq = window.__fbq || []).push([].slice.call(arguments)); };", ""))
        if storage_init:
            self.ctx.add_init_script(storage_init)
        base = env.base

        def handler(route, request):
            url = request.url
            if url.startswith(base):
                route.continue_()
            elif fbevents and "connect.facebook.net/en_US/fbevents.js" in url:
                route.fulfill(status=200, content_type="text/javascript", body="/* fbevents stub */")
            else:
                self.blocked.append(url)
                route.abort()

        self.ctx.route("**/*", handler)
        self.ctx.on("request", lambda r: self.requests.append((r.url, r.method, r.resource_type, r.post_data)))
        self.page = self.ctx.new_page()
        self.page.on("pageerror", lambda e: self.errors.append("pageerror: %s" % e))
        self.page.on("console", lambda m: self.errors.append("console: %s" % m.text) if m.type == "error" else None)
        if clock is not None:
            self.page.clock.set_fixed_time(clock)

    def goto(self, slug):
        self.page.goto(self.env.base + PAGE_PATH[slug])
        self.page.wait_for_load_state("load")
        return self.page

    def close(self):
        try:
            self.ctx.close()
        except Exception:   # noqa: BLE001
            pass


# ---------------------------------------------------------------------------------------------
# Static text helpers
# ---------------------------------------------------------------------------------------------
def strip_tags(h):
    h = re.sub(r"(?is)<(script|style|noscript)\b.*?</\1>", " ", h)
    h = re.sub(r"(?s)<!--.*?-->", " ", h)
    h = re.sub(r"<[^>]+>", " ", h)
    import html as _html
    return re.sub(r"\s+", " ", _html.unescape(h)).strip()


def head_of(text):
    return text[:text.index("</head>")]


def pixel_block(text):
    a = text.index("<!-- Meta Pixel Code -->")
    b = text.index("<!-- End Meta Pixel Code -->") + len("<!-- End Meta Pixel Code -->")
    return text[a:b]


def attr_values(text, attr):
    return re.findall(r'\b%s\s*=\s*"([^"]*)"' % attr, text)


def all_visible_strings(text):
    """Visible text, plus the attribute text a reader or a screen reader meets (placeholders, titles, labels)."""
    import html as _html
    extra = []
    for a in ("placeholder", "aria-label", "title", "alt", "content", "value"):
        extra += [_html.unescape(v) for v in attr_values(text, a)]
    return strip_tags(text) + " " + " ".join(extra)


def money_tokens(s):
    return set(re.findall(r"\$(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?(?: million)?", s))


def percent_tokens(s):
    return set(re.findall(r"\d+(?:\.\d+)?%", s))


# ---------------------------------------------------------------------------------------------
# static: the files themselves (head rules, pixel, sources, facts, held words, links)
# ---------------------------------------------------------------------------------------------
FORBIDDEN_JS = [
    (r"localStorage|sessionStorage|indexedDB|document\.cookie", "browser storage"),
    (r"\bfetch\s*\(|XMLHttpRequest|sendBeacon|WebSocket|EventSource|navigator\.serviceWorker|importScripts", "a network call"),
    (r"new\s+Image\s*\(|\.src\s*=|createElement\(\s*['\"](script|img|iframe|link|form)['\"]", "something that loads from elsewhere"),
    (r"navigator\.clipboard|\beval\s*\(|new\s+Function\s*\(|document\.write", "clipboard / eval / document.write"),
    (r"\bon(click|input|change|submit|load)\s*=", "an inline event handler"),
]


VOID_TAGS = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}
IMPLIED_END = {"p", "li", "td", "th", "tr", "thead", "tbody", "dt", "dd", "option"}


def well_formed(text):
    """(problems, duplicate ids): every end tag closes the right start tag, nothing is left open, ids are unique."""
    from html.parser import HTMLParser

    class P(HTMLParser):
        def __init__(self):
            super().__init__(convert_charrefs=True)
            self.stack, self.problems, self.ids = [], [], {}

        def handle_starttag(self, tag, attrs):
            d = dict(attrs)
            if "id" in d:
                self.ids[d["id"]] = self.ids.get(d["id"], 0) + 1
            if tag not in VOID_TAGS:
                self.stack.append((tag, self.getpos()))

        def handle_endtag(self, tag):
            if tag in VOID_TAGS:
                return
            while self.stack and self.stack[-1][0] != tag and self.stack[-1][0] in IMPLIED_END:
                self.stack.pop()
            if not self.stack:
                self.problems.append("stray </%s> at %s" % (tag, self.getpos()))
            elif self.stack[-1][0] != tag:
                self.problems.append("</%s> at %s closes <%s> from %s" % (tag, self.getpos(), self.stack[-1][0], self.stack[-1][1]))
                for i in range(len(self.stack) - 1, -1, -1):
                    if self.stack[i][0] == tag:
                        del self.stack[i:]
                        break
            else:
                self.stack.pop()

    p = P()
    p.feed(text)
    p.close()
    problems = p.problems + ["<%s> from %s is never closed" % (t, pos) for t, pos in p.stack if t not in IMPLIED_END]
    return problems, [k for k, v in p.ids.items() if v > 1]


def own_script(text):
    """The page's own inline script (not the pixel, not the JSON-LD)."""
    out = []
    for m in re.finditer(r"(?is)<script\b([^>]*)>(.*?)</script>", text):
        attrs, body = m.group(1), m.group(2)
        if "application/ld+json" in attrs or "src=" in attrs or "fbq('init'" in body:
            continue
        out.append(body)
    return "\n".join(out)


def link_exists(root, href):
    p = urlsplit(href).path
    rel = p.strip("/")
    if rel == "":
        return (root / "index.html").exists()
    return any((root / c).is_file() for c in (rel, rel + ".html", rel + "/index.html"))


def group_static(env, R, pages):
    ref = env.read("vs-yardbook.html")
    ref_pixel = pixel_block(ref)
    seen_titles, seen_desc = {}, {}
    for slug in pages:
        rel = env.page_file(slug)
        path = env.root / rel
        W = "static"
        R.check(W, "%s exists" % rel, path.exists())
        if not path.exists():
            continue
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        canon = BASE_URL + PAGE_PATH[slug]
        head = head_of(text)

        problems, dup_ids = well_formed(text)
        R.check(W, "%s: the HTML is well formed (every tag closed properly) and every id is unique" % rel, not problems and not dup_ids, (problems[:2], dup_ids))

        # --- the <head> rules
        off = raw.find(b"<meta charset")
        R.check(W, "%s: <meta charset> is one of the first 1024 bytes (at %d)" % (rel, off), 0 <= off < 1024 and text.count("<meta charset") == 1)
        R.check(W, "%s: html lang is en-AU and there is a viewport tag" % rel, '<html lang="en-AU">' in text and 'name="viewport"' in head)
        titles = re.findall(r"<title>(.*?)</title>", head, re.S)
        R.check(W, "%s: exactly one <title>, 20 to 70 characters" % rel, len(titles) == 1 and 20 <= len(strip_tags(titles[0])) <= 70, titles)
        descs = re.findall(r'<meta name="description" content="([^"]*)"', head)
        R.check(W, "%s: exactly one meta description, 70 to 160 characters" % rel, len(descs) == 1 and 70 <= len(descs[0]) <= 160, descs)
        canons = re.findall(r'<link rel="canonical" href="([^"]*)"', head)
        R.check(W, "%s: one canonical, %s" % (rel, canon), canons == [canon], canons)
        og = dict(re.findall(r'<meta property="og:([a-z:]+)" content="([^"]*)"', head))
        R.check(W, "%s: og:title, og:description, og:type, og:url (= canonical) and an absolute og:image" % rel,
                all(k in og and og[k] for k in ("title", "description", "type", "url", "image")) and og.get("url") == canon
                and og.get("image", "").startswith(BASE_URL + "/icons/"), og)
        if titles:
            seen_titles.setdefault(strip_tags(titles[0]), []).append(rel)
        if descs:
            seen_desc.setdefault(descs[0], []).append(rel)

        # --- the Meta Pixel block and attribution.js, exactly as on the existing pages
        R.check(W, "%s: the Meta Pixel block is identical to vs-yardbook.html's" % rel, "<!-- Meta Pixel Code -->" in text and pixel_block(text) == ref_pixel)
        R.check(W, "%s: attribution.js is loaded once, right after the pixel block" % rel,
                text.count('<script src="/attribution.js" defer></script>') == 1
                and re.search(r"<!-- End Meta Pixel Code -->\s*<script src=\"/attribution\.js\" defer></script>", text) is not None)

        # --- nothing else is loaded from anywhere
        srcs = re.findall(r'<script\b[^>]*\bsrc="([^"]*)"', text)
        R.check(W, "%s: the only external script is /attribution.js" % rel, srcs == ["/attribution.js"], srcs)
        R.check(W, "%s: no stylesheet links, @import or non-local url()" % rel,
                not re.search(r"<link[^>]+rel=\"stylesheet\"", text) and "@import" not in text and not re.search(r"url\((?!/fonts/)", text))
        hosts = set()
        for h in re.findall(r"https?://([a-z0-9.-]+)", text):
            hosts.add(h)
        R.check(W, "%s: every web address in the file is to a known host" % rel, hosts <= EXTERNAL_OK, sorted(hosts - EXTERNAL_OK))
        outside = set(re.findall(r"https?://([a-z0-9.-]+)", text.replace(ref_pixel, "")))
        R.check(W, "%s: outside the pixel block, nothing points at Facebook" % rel, not [h for h in outside if "facebook" in h], sorted(outside))

        own = own_script(text)
        bad = [label for rx, label in FORBIDDEN_JS if re.search(rx, own)]
        R.check(W, "%s: the page's own script uses no storage, network, clipboard or eval%s" % (rel, "" if own else " (it has no script)"), not bad, bad)

        # --- links
        apps = [h for h in attr_values(text, "href") if "app.keptsoftware.com.au" in h]
        R.check(W, "%s: every app link is exactly %s or %s (3 of them: header, CTA, CTA)" % (rel, "?industry=lawn_care", "?demo=1"),
                len(apps) == 3 and sorted(apps) == sorted([APP_FREE, APP_FREE, APP_DEMO]), apps)
        cta = re.search(r'(?s)<div class="cta-final">.*?</div>\s*</section>', text)
        R.check(W, "%s: exactly one calm CTA block, with no list in it" % rel,
                text.count('class="cta-final"') == 1 and cta is not None and "<li" not in cta.group(0) and len(re.findall(r"<p>", cta.group(0))) == 1)
        internal = [h for h in attr_values(text, "href") if h.startswith("/") and not h.startswith("//")]
        missing = [h for h in internal if not link_exists(env.root, h)]
        R.check(W, "%s: every internal link goes to a page that exists (%d links)" % (rel, len(internal)), not missing, missing)
        R.check(W, "%s: no javascript: links, and no target=_blank" % rel, "javascript:" not in text and 'target="_blank"' not in text)

        # --- words and numbers
        everything = all_visible_strings(text) + " " + " ".join(re.findall(r"(?s)<script type=\"application/ld\+json\">(.*?)</script>", text))
        held = [label for rx, label in HELD if re.search(rx, everything, re.I)] + [label for rx, label in HELD_CASE_SENSITIVE if re.search(rx, everything)]
        R.check(W, "%s: none of the held words (Pay now, automatic, tax invoice, trial, encryption, Marketplace, prices ...)" % rel, not held, held)
        visible = all_visible_strings(text)
        extra_money = money_tokens(visible) - ALLOWED_AMOUNTS[slug]
        R.check(W, "%s: no stray dollar amounts (only %s)" % (rel, ", ".join(sorted(ALLOWED_AMOUNTS[slug])) or "none"), not extra_money, sorted(extra_money))
        extra_pct = percent_tokens(visible) - ALLOWED_PERCENTS[slug]
        R.check(W, "%s: no stray percentages (only %s)" % (rel, ", ".join(sorted(ALLOWED_PERCENTS[slug])) or "none"), not extra_pct, sorted(extra_pct))
        plain_text = strip_tags(text)
        R.check(W, "%s: says Kept's tax tools are estimates, not professional advice" % rel, TAX_NOTE in plain_text)
        if slug in MUST_SAY:
            lacking = [s for s in MUST_SAY[slug] if s not in plain_text]
            R.check(W, "%s: says what FACTS.md says (%d statements)" % (rel, len(MUST_SAY[slug])), not lacking, lacking)

        # --- sources: the ATO links and their "page updated" dates
        ato_links = set(h for h in attr_values(text, "href") if "ato.gov.au" in h)
        if slug in SOURCES:
            want = set(ATO[k][0] for k in SOURCES[slug])
            lines_ok = True
            for k in SOURCES[slug]:
                url, updated = ATO[k]
                if not re.search(r'<a href="%s"[^>]*>[^<]+</a> \(page updated %s\)' % (re.escape(url), re.escape(updated)), text):
                    lines_ok = False
            faq_links = set(h for h in ato_links if h not in want)
            R.check(W, "%s: each ATO source link is listed with 'page updated <date>' as in FACTS.md" % rel, lines_ok, sorted(want))
            R.check(W, "%s: no ATO link other than the listed sources" % rel, ato_links <= want, sorted(faq_links))
            R.check(W, "%s: says when the ATO pages were checked" % rel, "Checked against the ATO pages on 24 October 2026" in plain_text)
        else:
            R.check(W, "%s: no ATO links on the index" % rel, not ato_links)

        # --- headings: one h1, no skipped levels
        levels = [int(m) for m in re.findall(r"<h([1-6])\b", text)]
        R.check(W, "%s: one h1 and headings never skip a level" % rel, levels.count(1) == 1 and levels[0] == 1 and all(b <= a + 1 for a, b in zip(levels, levels[1:])), levels)

        # --- structured data
        ld_blocks = re.findall(r'(?s)<script type="application/ld\+json">\s*(.*?)\s*</script>', text)
        if slug == "":
            R.check(W, "%s: no structured data (nothing on it to describe)" % rel, not ld_blocks)
            cards = re.findall(r'(?s)<article class="tcard">(.*?)</article>', text)
            hrefs = [re.search(r'href="(/free/[a-z-]+)"', c).group(1) if re.search(r'href="(/free/[a-z-]+)"', c) else None for c in cards]
            R.check(W, "%s: lists the five tools, each with a one-line description and a link" % rel,
                    len(cards) == 5 and sorted(hrefs) == sorted("/free/" + s for s in SLUGS) and all(len(re.findall(r"<p>", c)) == 1 for c in cards), hrefs)
        else:
            ok, why = False, ""
            try:
                ld = json.loads(ld_blocks[0])
                graph = ld["@graph"]
                app = [g for g in graph if g["@type"] == "WebApplication"][0]
                faq = [g for g in graph if g["@type"] == "FAQPage"][0]
                details = re.findall(r"(?s)<details>\s*<summary>(.*?)</summary>\s*<p>(.*?)</p>\s*</details>", text)
                import html as _html
                visible_faq = [(_html.unescape(q).strip(), re.sub(r"\s+", " ", _html.unescape(re.sub(r"<[^>]+>", "", a))).strip()) for q, a in details]
                json_faq = [(e["name"], e["acceptedAnswer"]["text"]) for e in faq["mainEntity"]]
                ok = (app["url"] == canon and app["name"] and app.get("isAccessibleForFree") is True and app["inLanguage"] == "en-AU"
                      and 3 <= len(visible_faq) <= 4 and visible_faq == json_faq)
                why = (app["url"], len(visible_faq), len(json_faq))
                if visible_faq != json_faq:
                    why = [x for x in zip(visible_faq, json_faq) if x[0] != x[1]][:1]
            except Exception as e:   # noqa: BLE001
                why = "%s: %s" % (type(e).__name__, e)
            R.check(W, "%s: JSON-LD is a WebApplication for this page plus a FAQPage that matches the 3-4 visible questions word for word" % rel, ok, why)

        R.check(W, "%s: a sensible size (under 120 KB)" % rel, len(raw) < 120000, len(raw))

    dup_t = {k: v for k, v in seen_titles.items() if len(v) > 1}
    dup_d = {k: v for k, v in seen_desc.items() if len(v) > 1}
    R.check("static", "titles are all different", not dup_t, dup_t)
    R.check("static", "descriptions are all different", not dup_d, dup_d)


# ---------------------------------------------------------------------------------------------
# helpers shared by the calculator groups
# ---------------------------------------------------------------------------------------------
BULK_JS = """([iid, oid, values]) => values.map(v => {
  const i = document.getElementById(iid);
  i.value = v;
  i.dispatchEvent(new Event('input', {bubbles: true}));
  const out = document.getElementById(oid);
  const o = {state: out.getAttribute('data-state'), text: out.textContent.trim(), invalid: i.getAttribute('aria-invalid'), n: out.querySelectorAll('[data-out]').length};
  out.querySelectorAll('[data-out]').forEach(e => { o[e.getAttribute('data-out')] = e.textContent; });
  return o;
})"""


def bulk(page, input_id, out_id, values):
    return page.evaluate(BULK_JS, [input_id, out_id, list(values)])


def fmt_num(x):
    """1234.50 -> '1,234.5', 5000.00 -> '5,000' (the way the pages show kilometres and hours)."""
    return format(D(x).normalize(), ",f")


def open_clean(env, slug, **kw):
    s = env.session(**kw)
    s.goto(slug)
    return s


def no_page_errors(R, group, label, s):
    R.check(group, "%s: no uncaught errors or console errors" % label, not s.errors, s.errors[:3])


# ---------------------------------------------------------------------------------------------
# gst
# ---------------------------------------------------------------------------------------------
GST_VALID = [("0", "0"), ("0.00", "0"), ("0.01", "0.01"), ("0.04", "0.04"), ("0.05", "0.05"), ("0.06", "0.06"), ("0.14", "0.14"),
             ("0.15", "0.15"), ("0.25", "0.25"), ("0.95", "0.95"), ("1", "1"), ("1.00", "1"), ("12.5", "12.5"), (".5", "0.5"),
             ("5.", "5"), ("200", "200"), ("220", "220"), ("$1,000,000", "1000000"), ("1,000,000.00", "1000000"),
             ("1000000", "1000000"), ("999,999,999.99", "999999999.99"), (" $ 1,234.56 ", "1234.56"), ("0000.10", "0.10"),
             ("9.99", "9.99"), ("19.99", "19.99"), ("33.33", "33.33")]
GST_ERRORS = [
    ("-1", "negative"), ("-0.01", "negative"), ("\u22125", "negative"), ("(5)", "negative"), ("$-5", "negative"), ("--5", "negative"),
    ("abc", "format"), ("1e3", "format"), ("12,50", "format"), ("1,2345", "format"), ("NaN", "format"), ("Infinity", "format"),
    ("1..2", "format"), ("1.2.3", "format"), ("$", "format"), (".", "format"), ("5-", "format"), ("12abc", "format"), ("0x10", "format"),
    ("\u0661\u0662", "format"), ("\uff11\uff12", "format"), ("1 2 3,4", "format"), ("$$5", "format"),
    ("0.995", "decimals"), ("19.995", "decimals"), ("10.001", "decimals"), ("1.234", "decimals"), ("999999999.999", "decimals"),
    ("1,000,000,000.00", "large"), ("1000000000", "large"), ("99999999999999999999", "large"), ("1,000,000,000", "large"),
]
GST_SNIPPET = {"negative": "$0 or more", "format": "not an amount", "decimals": "two digits after the decimal point", "large": "too large"}


def group_gst(env, R, pages):
    if "gst-calculator" not in pages:
        return
    W = "gst"
    s = open_clean(env, "gst-calculator")
    page = s.page
    no_page_errors(R, W, "gst-calculator", s)

    # the worked example in the facts
    r = bulk(page, "add-amount", "add-out", ["200"])[0]
    R.check(W, "add GST to $200: GST $20.00, total $220.00", (r["gst"], r["total"], r["before"]) == ("$20.00", "$220.00", "$200.00"), r)
    r = bulk(page, "rem-amount", "rem-out", ["220"])[0]
    R.check(W, "take GST out of $220: GST $20.00, price before GST $200.00", (r["gst"], r["before"], r["total"]) == ("$20.00", "$200.00", "$220.00"), r)

    # rounding, in both directions, with answers written out by hand
    hand_add = {"0": ("$0.00", "$0.00"), "0.01": ("$0.00", "$0.01"), "0.04": ("$0.00", "$0.04"), "0.05": ("$0.01", "$0.06"),
                "0.14": ("$0.01", "$0.15"), "0.15": ("$0.02", "$0.17"), "1": ("$0.10", "$1.10"), "1000000": ("$100,000.00", "$1,100,000.00")}
    got = dict(zip(hand_add, bulk(page, "add-amount", "add-out", list(hand_add))))
    bad = {k: (got[k]["gst"], got[k]["total"]) for k in hand_add if (got[k]["gst"], got[k]["total"]) != hand_add[k]}
    R.check(W, "add GST: $0 $0.01 $0.04 $0.05 (half a cent rounds up) $0.14 $0.15 $1 $1,000,000 match the hand-worked answers", not bad, bad)
    hand_rem = {"0": ("$0.00", "$0.00"), "0.05": ("$0.00", "$0.05"), "0.06": ("$0.01", "$0.05"), "1": ("$0.09", "$0.91"), "1000000": ("$90,909.09", "$909,090.91")}
    got = dict(zip(hand_rem, bulk(page, "rem-amount", "rem-out", list(hand_rem))))
    bad = {k: (got[k]["gst"], got[k]["before"]) for k in hand_rem if (got[k]["gst"], got[k]["before"]) != hand_rem[k]}
    R.check(W, "take GST out: $0 $0.05 $0.06 $1 $1,000,000 match the hand-worked answers", not bad, bad)

    # every typed form against the decimal oracle
    typed = [t for t, _ in GST_VALID]
    for label, in_id, out_id, fn in (("add", "add-amount", "add-out", gst_add), ("take out", "rem-amount", "rem-out", gst_remove)):
        res = bulk(page, in_id, out_id, typed)
        bad = []
        for (t, v), r in zip(GST_VALID, res):
            before, gst, total = fn(D(v))
            want = (money(before), money(gst), money(total))
            if r["state"] != "ok" or (r["before"], r["gst"], r["total"]) != want or r["invalid"] is not None:
                bad.append((t, want, r))
        R.check(W, "%s GST: %d typed amounts ($0 to $999,999,999.99, with $ and commas) agree with the decimal oracle" % (label, len(typed)), not bad, bad[:2])

    # a sweep: every amount up to $3.00 and 700 seeded random ones, both directions
    rnd = random.Random(20261024)
    cents = list(range(0, 301)) + [rnd.randrange(0, 99999999999) for _ in range(500)] + [rnd.randrange(0, 100000) for _ in range(200)]
    typed = ["%d.%02d" % (c // 100, c % 100) for c in cents]
    for label, in_id, out_id, fn in (("add", "add-amount", "add-out", gst_add), ("take out", "rem-amount", "rem-out", gst_remove)):
        res = bulk(page, in_id, out_id, typed)
        bad = []
        for c, t, r in zip(cents, typed, res):
            before, gst, total = fn(D(c) / 100)
            if (r["before"], r["gst"], r["total"]) != (money(before), money(gst), money(total)):
                bad.append((t, (money(before), money(gst), money(total)), (r.get("before"), r.get("gst"), r.get("total"))))
        R.check(W, "%s GST: sweep of %d amounts agrees with the decimal oracle to the cent" % (label, len(cents)), not bad, bad[:3])
        # the parts always add up to the whole
        sums_ok = True
        for t, r in zip(typed, res):
            parse = lambda x: D(x.replace("$", "").replace(",", ""))   # noqa: E731
            if parse(r["before"]) + parse(r["gst"]) != parse(r["total"]):
                sums_ok = False
                break
        R.check(W, "%s GST: price before GST plus GST always equals the total (no penny lost)" % label, sums_ok)

    # things that are not amounts
    for in_id, out_id in (("add-amount", "add-out"), ("rem-amount", "rem-out")):
        res = bulk(page, in_id, out_id, [t for t, _ in GST_ERRORS])
        bad = []
        for (t, why), r in zip(GST_ERRORS, res):
            ok = (r["state"] == "error" and r["n"] == 0 and r["invalid"] == "true" and GST_SNIPPET[why] in r["text"])
            if not ok:
                bad.append((t, why, r["state"], r["text"][:80]))
        R.check(W, "%s: %d bad entries (negative, text, 1e3, 12,50, .995, too big, ...) each get an error that says what to fix, and no number" % (in_id, len(GST_ERRORS)), not bad, bad[:3])
        res = bulk(page, in_id, out_id, ["", "   ", "\u00a0"])
        R.check(W, "%s: empty is a calm prompt, not an error" % in_id, all(r["state"] == "empty" and r["n"] == 0 and r["invalid"] is None for r in res), res)
        res = bulk(page, in_id, out_id, ["12", "abc", "13"])
        R.check(W, "%s: a good amount after a bad one clears the error" % in_id, res[2]["state"] == "ok" and res[2]["invalid"] is None, res[2])
    # typing for real, a key at a time
    page.fill("#add-amount", "")
    page.locator("#add-amount").press_sequentially("1,234.56")
    R.check(W, "typing 1,234.56 key by key ends on GST $123.46 (123.456 rounded) and total $1,358.02",
            (page.text_content("#add-out [data-out=gst]"), page.text_content("#add-out [data-out=total]")) == ("$123.46", "$1,358.02"))
    s.close()

    # the rounding rule is stated
    text = strip_tags(env.read("free/gst-calculator.html"))
    R.check(W, "the page says the rounding rule: nearest cent, half a cent up", "rounded to the nearest cent, with half a cent rounded up" in text)


# ---------------------------------------------------------------------------------------------
# km
# ---------------------------------------------------------------------------------------------
KM_VALID = ["0", "0.00", "0.01", "0.5", ".5", "1", "2514", "2,514", "2514.25", "4999", "4,999", "4999.99", "5000", "5,000", "5000.00", "1,000", " 3 000 "]
KM_OVER = ["5001", "5,001", "5000.01", "5000.5", "6000", "10000", "1000000", "99999999999999999999", "123456789012345678"]
KM_ERRORS = [("-1", "Enter 0 or more"), ("\u22125", "Enter 0 or more"), ("(5)", "Enter 0 or more"), ("abc", "not a distance"), ("1e3", "not a distance"),
             ("12,50", "not a distance"), ("$5", "not a distance"), ("5 km", "not a distance"), ("1..2", "not a distance"), (".", "not a distance"),
             ("1.234", "two digits after the decimal point"), ("4999.999", "two digits after the decimal point")]


def group_km(env, R, pages):
    if "cents-per-km-calculator" not in pages:
        return
    W = "km"
    s = open_clean(env, "cents-per-km-calculator")
    page = s.page
    no_page_errors(R, W, "cents-per-km-calculator", s)
    opts = page.evaluate("Array.from(document.querySelectorAll('#km-year option')).map(o => [o.value, o.textContent.trim()])")
    want = [["2026-27", "2026-27: 91 cents per km"], ["2025-26", "2025-26: 88 cents per km"], ["2024-25", "2024-25: 88 cents per km"]]
    R.check(W, "the year selector offers 2026-27 (91 cents), 2025-26 (88) and 2024-25 (88), in that order", opts == want, opts)
    R.check(W, "the selector starts on 2026-27", page.eval_on_selector("#km-year", "e => e.value") == "2026-27")

    for year, rate in KM_RATES.items():
        page.select_option("#km-year", year)
        res = bulk(page, "km-input", "km-out", KM_VALID)
        bad = []
        for t, r in zip(KM_VALID, res):
            km = D(t.replace(",", "").replace(" ", ""))
            want_ded = money(km * rate / 100)
            if r["state"] != "ok" or r["deduction"] != want_ded or r["rate"] != "%d cents per km" % rate or r["km"] != fmt_num(km) + " km":
                bad.append((t, want_ded, r))
        R.check(W, "%s (%d cents): %d distances from 0 to exactly 5,000 km give kilometres x rate to the cent" % (year, rate, len(KM_VALID)), not bad, bad[:2])
        # the boundary, one case at a time
        for t, expect in (("0", "$0.00"), ("1", money(D(rate) / 100)), ("4999", money(D(4999) * rate / 100)), ("5000", money(D(5000) * rate / 100))):
            r = bulk(page, "km-input", "km-out", [t])[0]
            R.check(W, "%s: %s km is %s" % (year, t, expect), r["state"] == "ok" and r["deduction"] == expect, r)
        r = bulk(page, "km-input", "km-out", ["5000"])[0]
        R.check(W, "%s: at exactly 5,000 km it says that is the most the method allows" % year, "most this method allows" in r["text"], r["text"])
        r = bulk(page, "km-input", "km-out", ["5001"])[0]
        R.check(W, "%s: 5,001 km gives no figure: it says the method does not apply and to ask an accountant" % year,
                r["state"] == "over" and r["n"] == 0 and "$" not in r["text"] and not re.search(r"\d+\.\d\d", r["text"].replace("5,001", ""))
                and "does not apply" in r["text"] and "ask your accountant" in r["text"] and "5,000" in r["text"], r)
        res = bulk(page, "km-input", "km-out", KM_OVER)
        bad = [(t, r["state"], r["text"][:70]) for t, r in zip(KM_OVER, res)
               if not (r["state"] == "over" and r["n"] == 0 and "$" not in r["text"] and "accountant" in r["text"] and r["invalid"] is None)]
        R.check(W, "%s: %d distances above 5,000 km (5001, 5000.01, a million, 20 digits ...) all give no figure and no $" % (year, len(KM_OVER)), not bad, bad[:3])
        res = bulk(page, "km-input", "km-out", [t for t, _ in KM_ERRORS])
        bad = [(t, r["state"], r["text"][:60]) for (t, why), r in zip(KM_ERRORS, res) if not (r["state"] == "error" and r["n"] == 0 and r["invalid"] == "true" and why in r["text"])]
        R.check(W, "%s: %d bad entries each get an error that says what to fix, and no number" % (year, len(KM_ERRORS)), not bad, bad[:3])
    res = bulk(page, "km-input", "km-out", ["", "  "])
    R.check(W, "empty is a calm prompt, not an error", all(r["state"] == "empty" and r["n"] == 0 and r["invalid"] is None for r in res), res)

    # the ATO's own worked example: 2,514 km in 2025-26 at 88 cents is $2,212.32 (the ATO rounds it to $2,212)
    page.select_option("#km-year", "2025-26")
    r = bulk(page, "km-input", "km-out", ["2514"])[0]
    R.check(W, "2,514 km in 2025-26 is $2,212.32 (the ATO's own example, which it rounds to $2,212)", r.get("deduction") == "$2,212.32", r)
    # changing the year updates a figure that is already there, and an over-cap one
    page.fill("#km-input", "1000")
    page.select_option("#km-year", "2026-27")
    a = page.text_content("#km-out [data-out=deduction]")
    page.select_option("#km-year", "2024-25")
    b = page.text_content("#km-out [data-out=deduction]")
    R.check(W, "changing the year re-works the figure for 1,000 km: $910.00 then $880.00", (a, b) == ("$910.00", "$880.00"), (a, b))
    page.fill("#km-input", "5001")
    page.select_option("#km-year", "2026-27")
    R.check(W, "changing the year keeps the over-5,000 km message", page.get_attribute("#km-out", "data-state") == "over")
    s.close()

    text = env.read("free/cents-per-km-calculator.html")
    table = strip_tags(re.search(r"(?s)<table role=\"table\" class=\"rate-table\">.*?</table>", text).group(0))
    exp = "Income year Rate 5,000 km at this rate 2026-27 91 cents per km %s 2025-26 88 cents per km %s 2024-25 88 cents per km %s" % (
        money(D(5000) * 91 / 100), money(D(5000) * 88 / 100), money(D(5000) * 88 / 100))
    R.check(W, "the rates table shows each year's rate and what 5,000 km comes to", table == exp, table)


# ---------------------------------------------------------------------------------------------
# bas
# ---------------------------------------------------------------------------------------------
BAS_READ = """() => {
  const card = id => { const e = document.getElementById(id), t = e.querySelector('time');
    return {state: e.getAttribute('data-state'), date: e.getAttribute('data-date'), days: e.getAttribute('data-days'),
            time: t ? t.textContent : null, datetime: t ? t.getAttribute('datetime') : null, text: e.textContent.replace(/\\s+/g, ' ').trim()}; };
  const rows = id => Array.from(document.querySelectorAll('#' + id + ' tr[data-due]')).map(r => { const t = r.querySelector('time'), sub = r.querySelector('.sub'), tag = r.querySelector('.tag');
    return {due: r.getAttribute('data-due'), eff: r.getAttribute('data-eff'), cls: r.className, shown: t && t.getAttribute('datetime'), shownText: t && t.textContent,
            sub: sub ? sub.textContent : '', tag: tag ? tag.textContent : ''}; });
  return {q: card('next-quarterly'), m: card('next-monthly'), qrows: rows('tbl-quarterly'), mrows: rows('tbl-monthly')};
}"""


def bas_expect(instant, tz):
    zone = tz if tz.startswith("Australia/") else "Australia/Sydney"
    today = instant.astimezone(ZoneInfo(zone)).date()
    return today, next_due(BAS_QUARTERLY, today), next_due(BAS_MONTHLY, today)


def bas_check(R, W, label, got, today, nq, nm):
    for key, dates, nxt, name in (("q", BAS_QUARTERLY, nq, "quarterly"), ("m", BAS_MONTHLY, nm, "monthly")):
        card = got[key]
        rows = got[key + "rows"]
        if nxt is None:
            ok = (card["state"] == "none" and card["date"] is None and card["time"] is None and "2027-28" in card["text"] and "ATO" in card["text"]
                  and all(r["cls"] == "is-past" and r["tag"] == "Passed" for r in rows))
        else:
            days = (nxt - today).days
            effs = [effective(d) for d in dates]
            want_cls = ["is-past" if e < today else ("is-next" if e == nxt else "") for e in effs]
            ok = (card["state"] == ("today" if days == 0 else "next") and card["date"] == nxt.isoformat() and card["datetime"] == nxt.isoformat()
                  and card["days"] == str(days) and card["time"] == nice(nxt) and when_phrase(days) in card["text"]
                  and [r["cls"] for r in rows] == want_cls
                  and [r["tag"] for r in rows] == [{"is-past": "Passed", "is-next": "Next", "": ""}[c] for c in want_cls])
        R.check(W, "%s: next %s BAS is %s" % (label, name, "none left (says so)" if nxt is None else "%s, %s" % (nice(nxt), when_phrase((nxt - today).days))), ok, (card, [r["cls"] for r in rows]))


def group_bas(env, R, pages):
    if "bas-due-dates" not in pages:
        return
    W = "bas"
    # the table itself: dates, weekdays and the weekend rule, read from the page
    s = open_clean(env, "bas-due-dates", clock=datetime(2026, 10, 24, 10, 0, tzinfo=timezone(timedelta(hours=10))))
    page = s.page
    no_page_errors(R, W, "bas-due-dates", s)
    got = page.evaluate(BAS_READ)
    for key, dates, name in (("qrows", BAS_QUARTERLY, "quarterly"), ("mrows", BAS_MONTHLY, "monthly")):
        rows = got[key]
        bad = []
        for r, d in zip(rows, dates):
            e = effective(d)
            sub_ok = (not r["sub"]) if e == d else (DAYNAMES[d.weekday()] in r["sub"] and "next business day" in r["sub"] and "%d %s %d" % (d.day, MONTHNAMES[d.month - 1], d.year) in r["sub"])
            if (r["due"], r["eff"], r["shown"], r["shownText"]) != (d.isoformat(), e.isoformat(), e.isoformat(), nice(e)) or not sub_ok:
                bad.append((d, e, r))
        R.check(W, "%s table: %d dates, each shown on the right day, a Saturday or Sunday moved to the Monday" % (name, len(dates)), len(rows) == len(dates) and not bad, bad[:2])
    R.check(W, "the quarterly dates are 28 Oct 2026, 28 Feb 2027, 28 Apr 2027 and 28 Jul 2027 (F-BAS-1); 28 Feb 2027 is a Sunday so it shows Monday 1 March 2027",
            [r["due"] for r in got["qrows"]] == ["2026-10-28", "2027-02-28", "2027-04-28", "2027-07-28"] and got["qrows"][1]["shownText"] == "Monday 1 March 2027")
    R.check(W, "the monthly dates are the 21st of the month after each of July 2026 to June 2027 (F-BAS-2)",
            [r["due"] for r in got["mrows"]] == [d.isoformat() for d in BAS_MONTHLY] and got["mrows"][0]["due"] == "2026-08-21")

    # the real day: Saturday 24 October 2026
    today, nq, nm = bas_expect(datetime(2026, 10, 24, 10, 0, tzinfo=timezone(timedelta(hours=10))), "Australia/Brisbane")
    bas_check(R, W, "24 Oct 2026", got, today, nq, nm)

    # every boundary: the day before, the day of, the day after, for each date and for its weekend-adjusted date
    days = {date(2026, 6, 30), date(2026, 7, 1), date(2027, 6, 30), date(2027, 7, 1), date(2027, 7, 22), date(2027, 7, 29), date(2028, 1, 1), date(2030, 6, 1)}
    for d in BAS_QUARTERLY + BAS_MONTHLY:
        e = effective(d)
        for x in (d - timedelta(days=1), d, d + timedelta(days=1), e - timedelta(days=1), e, e + timedelta(days=1)):
            days.add(x)
    bad_runs = []
    for x in sorted(days):
        inst = datetime(x.year, x.month, x.day, 10, 0, tzinfo=timezone(timedelta(hours=10)))
        s2 = open_clean(env, "bas-due-dates", clock=inst)
        g = s2.page.evaluate(BAS_READ)
        t, a, b = bas_expect(inst, "Australia/Brisbane")
        sub = Results(echo=False)
        bas_check(sub, W, x.isoformat(), g, t, a, b)
        bad_runs += [(x.isoformat(), r[1], r[3]) for r in sub.failed]
        if s2.errors:
            bad_runs.append((x.isoformat(), "page error", s2.errors[:1]))
        s2.close()
    R.check(W, "%d different days, 1 July 2026 to 2030 (the day before, the day of and the day after every quarterly and monthly date, 30 June and 1 July 2027, past the last date): quarterly and monthly 'next due' and the table marks are right" % len(days),
            not bad_runs, bad_runs[:3])
    for label, x, want_text in (("1 July 2026", date(2026, 7, 1), "Friday 21 August 2026"), ("30 June 2027", date(2027, 6, 30), "Wednesday 21 July 2027"),
                                ("1 July 2027", date(2027, 7, 1), "Wednesday 21 July 2027")):
        inst = datetime(x.year, x.month, x.day, 10, 0, tzinfo=timezone(timedelta(hours=10)))
        s2 = open_clean(env, "bas-due-dates", clock=inst)
        g = s2.page.evaluate(BAS_READ)
        s2.close()
        R.check(W, "%s: next monthly is %s and next quarterly is %s" % (label, want_text, "Wednesday 28 October 2026" if x.year == 2026 else "Wednesday 28 July 2027"),
                g["m"]["time"] == want_text and g["q"]["time"] == ("Wednesday 28 October 2026" if x.year == 2026 else "Wednesday 28 July 2027"), (g["q"]["time"], g["m"]["time"]))
    s2 = open_clean(env, "bas-due-dates", clock=datetime(2027, 7, 29, 10, 0, tzinfo=timezone(timedelta(hours=10))))
    g = s2.page.evaluate(BAS_READ)
    s2.close()
    R.check(W, "past the last date (29 July 2027): both boxes say every 2026-27 date has passed, point to the ATO page, and invent no date",
            g["q"]["state"] == "none" and g["m"]["state"] == "none" and "has passed" in g["q"]["text"] and "ATO page linked below" in g["q"]["text"] and not re.search(r"\b2027-28 (?:due|date) is", g["q"]["text"]), g["q"])

    # midnight and time zones: the date is the Australian date, in the visitor's zone if it is an Australian one, otherwise Sydney's
    brisbane = timezone(timedelta(hours=10))
    cases = [
        ("Brisbane 23:59:59 on 27 Oct", datetime(2026, 10, 27, 23, 59, 59, tzinfo=brisbane), "Australia/Brisbane"),
        ("Brisbane 00:00:00 on 28 Oct", datetime(2026, 10, 28, 0, 0, 0, tzinfo=brisbane), "Australia/Brisbane"),
        ("Brisbane 23:59:59 on 28 Oct", datetime(2026, 10, 28, 23, 59, 59, tzinfo=brisbane), "Australia/Brisbane"),
        ("Brisbane 00:00:00 on 29 Oct", datetime(2026, 10, 29, 0, 0, 0, tzinfo=brisbane), "Australia/Brisbane"),
        ("Perth, 23:30 on 27 Oct (it is already the 28th in Brisbane)", datetime(2026, 10, 27, 23, 30, tzinfo=timezone(timedelta(hours=8))), "Australia/Perth"),
        ("Adelaide, 00:15 on 28 Oct (still the 27th in Brisbane)", datetime(2026, 10, 27, 13, 45, tzinfo=timezone.utc), "Australia/Adelaide"),
        ("Sydney, 00:30 on 28 Oct (still the 27th in Brisbane)", datetime(2026, 10, 27, 13, 30, tzinfo=timezone.utc), "Australia/Sydney"),
        ("a device in New York, 20:00 on 27 Oct there (28 Oct, 11:00 in Sydney)", datetime(2026, 10, 27, 20, 0, tzinfo=timezone(timedelta(hours=-4))), "America/New_York"),
        ("a device on UTC, 13:30 on 27 Oct there (28 Oct, 00:30 in Sydney)", datetime(2026, 10, 27, 13, 30, tzinfo=timezone.utc), "UTC"),
        ("a device in Auckland, 02:00 on 29 Oct there (28 Oct, 00:00 in Sydney)", datetime(2026, 10, 28, 13, 0, tzinfo=timezone.utc), "Pacific/Auckland"),
    ]
    for label, inst, tz in cases:
        s2 = open_clean(env, "bas-due-dates", clock=inst, tz=tz)
        g = s2.page.evaluate(BAS_READ)
        s2.close()
        t, a, b = bas_expect(inst, tz)
        sub = Results(echo=False)
        bas_check(sub, W, label, g, t, a, b)
        R.check(W, "time zone: %s: the page counts it as %s" % (label, t.isoformat()), not sub.failed, [(r[1], r[3]) for r in sub.failed][:1])
    s.close()

    text = strip_tags(env.read("free/bas-due-dates.html"))
    R.check(W, "the online-lodgment extension wording is exactly the wording in FACTS.md (F-BAS-3), in the page and in the FAQ", text.count(F_BAS_3) >= 2, text.count(F_BAS_3))
    R.check(W, "the page links the ATO due-dates page (F-BAS-1..4)", ATO["bas"][0] in env.read("free/bas-due-dates.html"))


# ---------------------------------------------------------------------------------------------
# hourly
# ---------------------------------------------------------------------------------------------
HOURLY_BULK = """(rows) => rows.map(r => {
  const set = (id, v) => { const e = document.getElementById(id); e.value = v; e.dispatchEvent(new Event('input', {bubbles: true})); };
  set('h-income', r.income); set('h-weeks', r.weeks); set('h-hours', r.hours); set('h-costs', r.costs);
  const g = document.getElementById('h-gst'); if (g.checked !== r.gst) { g.checked = r.gst; g.dispatchEvent(new Event('change', {bubbles: true})); }
  const out = document.getElementById('h-out');
  const o = {state: out.getAttribute('data-state'), text: out.textContent.replace(/\\s+/g, ' ').trim(), invalid: ['h-income','h-weeks','h-hours','h-costs'].filter(id => document.getElementById(id).getAttribute('aria-invalid') === 'true')};
  out.querySelectorAll('[data-out]').forEach(e => { o[e.getAttribute('data-out')] = e.textContent; });
  return o; })"""


def hourly_oracle(income, weeks, hours, costs):
    income, weeks, hours, costs = D(income), D(weeks), D(hours), D(costs)
    total = income + costs
    hrs = weeks * hours
    rate = q2(total / hrs)
    gst = q2(rate * D("0.1"))
    return total, hrs, rate, gst, rate + gst


def group_hourly(env, R, pages):
    if "hourly-rate-calculator" not in pages:
        return
    W = "hourly"
    s = open_clean(env, "hourly-rate-calculator")
    page = s.page
    no_page_errors(R, W, "hourly-rate-calculator", s)

    def run(rows):
        return page.evaluate(HOURLY_BULK, rows)

    base = dict(income="80000", weeks="46", hours="25", costs="20000", gst=False)
    r = run([base])[0]
    R.check(W, "$80,000 + $20,000 costs over 46 weeks x 25 hours is $86.96 an hour, GST off: no GST rows",
            r["state"] == "ok" and r["rate-ex"] == "$86.96" and r["needed"] == "$100,000.00" and r["hours"] == "1,150" and "rate-inc" not in r and "gst" not in r, r)
    r = run([dict(base, gst=True)])[0]
    R.check(W, "the same with GST on: $86.96 before GST, $8.70 GST, $95.66 including GST", (r.get("rate-ex"), r.get("gst"), r.get("rate-inc")) == ("$86.96", "$8.70", "$95.66"), r)
    r = run([dict(base, gst=False)])[0]
    R.check(W, "switching GST off again removes the GST rows", "rate-inc" not in r and "gst" not in r, r)
    r = run([dict(income="8.95", weeks="1", hours="1", costs="0", gst=True)])[0]
    R.check(W, "a rate of $8.95: GST is 89.5 cents, which rounds up to $0.90 (total $9.85)", (r.get("rate-ex"), r.get("gst"), r.get("rate-inc")) == ("$8.95", "$0.90", "$9.85"), r)

    # a sweep of valid combinations against the decimal oracle
    rnd = random.Random(24102026)
    rows, exp = [], []
    for _ in range(300):
        inc = "%d.%02d" % (rnd.randrange(1, 400000), rnd.randrange(0, 100)) if rnd.random() < .5 else str(rnd.randrange(1, 400000))
        cost = "%d.%02d" % (rnd.randrange(0, 90000), rnd.randrange(0, 100)) if rnd.random() < .5 else str(rnd.randrange(0, 90000))
        weeks = str(rnd.randrange(1, 53))
        hrs = "%d.%d" % (rnd.randrange(1, 168), rnd.randrange(0, 10)) if rnd.random() < .4 else str(rnd.randrange(1, 169))
        if D(hrs) > 168:
            hrs = "168"
        gst = rnd.random() < .5
        rows.append(dict(income=inc, weeks=weeks, hours=hrs, costs=cost, gst=gst))
        exp.append(hourly_oracle(inc, weeks, hrs, cost))
    res = run(rows)
    bad = []
    for row, e, r in zip(rows, exp, res):
        total, hrs, rate, gst, inc = e
        want = {"needed": money(total), "hours": fmt_num(hrs), "rate-ex": money(rate)}
        if row["gst"]:
            want.update({"gst": money(gst), "rate-inc": money(inc)})
        if r["state"] != "ok" or any(r.get(k) != v for k, v in want.items()) or (not row["gst"] and "rate-inc" in r):
            bad.append((row, want, r))
    R.check(W, "300 seeded combinations (decimal hours, cents, GST on and off) agree with the decimal oracle to the cent", not bad, bad[:2])

    # zero, silly and huge
    cases = [
        (dict(base, hours="0"), {"hours"}), (dict(base, weeks="0"), {"weeks"}), (dict(base, weeks="0", hours="0"), {"weeks", "hours"}),
        (dict(base, weeks="53"), {"weeks"}), (dict(base, weeks="-1"), {"weeks"}), (dict(base, weeks="46.5"), {"weeks"}), (dict(base, weeks="abc"), {"weeks"}),
        (dict(base, hours="169"), {"hours"}), (dict(base, hours="168.1"), {"hours"}), (dict(base, hours="0.5"), {"hours"}), (dict(base, hours="-3"), {"hours"}),
        (dict(base, hours="22.55"), {"hours"}), (dict(base, hours="1e2"), {"hours"}), (dict(base, hours="99999999999999999999"), {"hours"}),
        (dict(base, income="0"), {"income"}), (dict(base, income="-5"), {"income"}), (dict(base, income="abc"), {"income"}), (dict(base, income="12,50"), {"income"}),
        (dict(base, income="1.234"), {"income"}), (dict(base, income="100,000,000.01"), {"income"}), (dict(base, income="1000000000000"), {"income"}),
        (dict(base, income="99999999999999999999"), {"income"}),
        (dict(base, costs="-1"), {"costs"}), (dict(base, costs="x"), {"costs"}), (dict(base, costs="100000000.01"), {"costs"}), (dict(base, costs="1e9"), {"costs"}),
        (dict(base, income="0", weeks="0", hours="0", costs="-1"), {"income", "weeks", "hours", "costs"}),
    ]
    res = run([c for c, _ in cases])
    bad = []
    for (c, want), r in zip(cases, res):
        ok = (r["state"] == "error" and set(x[2:] for x in r["invalid"]) == want and "rate-ex" not in r and "Check these boxes" in r["text"])
        if not ok:
            bad.append((c, want, r["state"], r["invalid"], r["text"][:90]))
    R.check(W, "%d silly inputs (zero hours, zero weeks, 53 weeks, 169 hours, negatives, text, too many decimals, huge numbers) each flag exactly the right boxes, say what to fix, and give no rate" % len(cases), not bad, bad[:3])
    res = run([c for c, _ in cases])
    R.check(W, "no result ever shows NaN, Infinity, undefined or null", not any(re.search(r"NaN|Infinity|undefined|null", r["text"]) for r in res))
    r = run([dict(base, hours="0")])[0]
    R.check(W, "zero hours explains why: no rate can be worked out from zero hours", "zero hours" in r["text"] and "1 to 168" in r["text"], r["text"])
    r = run([dict(base, weeks="0")])[0]
    R.check(W, "zero weeks explains why: no rate can be worked out from zero weeks", "zero weeks" in r["text"] and "1 to 52" in r["text"], r["text"])

    # the limits are allowed, and empty things are prompts
    ok_cases = [dict(base, weeks="1", hours="1"), dict(base, weeks="52", hours="168"), dict(base, hours="22.5"), dict(base, costs="0"), dict(base, costs="0.00"),
                dict(income="100,000,000", weeks="1", hours="1", costs="100,000,000", gst=True), dict(income="0.01", weeks="52", hours="168", costs="0", gst=True)]
    res = run(ok_cases)
    bad = []
    for c, r in zip(ok_cases, res):
        total, hrs, rate, gst, inc = hourly_oracle(c["income"].replace(",", ""), c["weeks"], c["hours"], c["costs"].replace(",", ""))
        if r["state"] != "ok" or r["rate-ex"] != money(rate) or (c["gst"] and r["rate-inc"] != money(inc)) or re.search(r"NaN|Infinity", r["text"]):
            bad.append((c, money(rate), r))
    R.check(W, "the limits work: 1 week x 1 hour, 52 weeks x 168 hours, 22.5 hours, $0 costs, $100,000,000 + $100,000,000, $0.01 income", not bad, bad[:2])
    res = run([dict(income="", weeks="", hours="", costs="", gst=False), dict(base, costs=""), dict(base, income="")])
    R.check(W, "empty boxes are a calm prompt that says which are still needed (not an error)",
            all(r["state"] == "empty" and not r["invalid"] and "Still to do" in r["text"] for r in res) and "business costs" in res[1]["text"] and "income you want" in res[2]["text"], res)
    r = run([dict(base, costs="")])[0]
    R.check(W, "an empty costs box is not silently treated as $0: it asks for 0 to be typed", "Type 0" in r["text"] and "rate-ex" not in r, r["text"])
    s.close()


# ---------------------------------------------------------------------------------------------
# quote template
# ---------------------------------------------------------------------------------------------
VETTED = {   # the service names Kept offers for each trade (meta-ads-pack.md and APP-CLAIMS.md)
    "lawn_care": ["Mowing", "Garden", "Washing", "Hedges", "Turf/Reno", "Weed spray"],
    "pressure_washing": ["Washing", "Roof", "Soft wash", "House exterior", "Gutters"],
    "cleaning": ["Regular clean", "Bond clean", "One-off clean", "Office", "Commercial", "Carpet"],
    "handyman": ["General handyman", "Day rate", "Flat-pack assembly", "Mounting & hanging", "Doors & locks", "Repair + materials"],
}
TRADE_LABELS = {"lawn_care": "Lawn care", "pressure_washing": "Pressure washing", "cleaning": "Cleaning", "handyman": "Handyman"}

Q_STATE_JS = """() => {
  const body = document.getElementById('q-lines'), out = document.getElementById('q-out');
  const v = k => out.querySelector('[data-out=' + k + ']').textContent;
  const errs = document.getElementById('q-errs');
  return {
    lines: Array.from(body.children).map(tr => ({d: tr.querySelector('[data-f=d]').value, q: tr.querySelector('[data-f=q]').value, p: tr.querySelector('[data-f=p]').value,
      amt: tr.querySelector('[data-f=amt]').textContent, inv: ['d', 'q', 'p'].filter(k => tr.querySelector('[data-f=' + k + ']').getAttribute('aria-invalid') === 'true').join(''),
      rm: tr.querySelector('[data-f=rm]').getAttribute('aria-label')})),
    totals: {state: out.getAttribute('data-state'), subtotal: v('subtotal'), gst: v('gst'), total: v('total'), label: document.getElementById('q-label-total').textContent,
             subVisible: !document.getElementById('q-row-sub').hidden, gstVisible: !document.getElementById('q-row-gst').hidden, errs: errs.hidden ? '' : errs.textContent.replace(/\\s+/g, ' ').trim()},
    chips: Array.from(document.querySelectorAll('#q-chips button')).map(b => b.textContent),
    note: document.getElementById('q-trade-note').textContent, status: document.getElementById('q-status').textContent,
    focus: document.activeElement ? (document.activeElement.getAttribute('data-f') || document.activeElement.id || document.activeElement.tagName) : ''
  };
}"""

Q_SET_JS = """(spec) => {
  const body = document.getElementById('q-lines');
  while (body.children.length < spec.lines.length) document.querySelector('#q-chips button[data-add=""]').click();
  while (body.children.length > spec.lines.length) body.lastElementChild.querySelector('[data-f=rm]').click();
  spec.lines.forEach((l, i) => { const tr = body.children[i];
    [['d', l[0]], ['q', l[1]], ['p', l[2]]].forEach(([k, val]) => { const e = tr.querySelector('[data-f=' + k + ']'); e.value = val; e.dispatchEvent(new Event('input', {bubbles: true})); }); });
  const g = document.getElementById('q-gst'); if (g.checked !== spec.gst) { g.checked = spec.gst; g.dispatchEvent(new Event('change', {bubbles: true})); }
}"""


def quote_oracle(lines, gst_on):
    amts = []
    for d, q, p in lines:
        if q.strip() == "" or p.strip() == "":
            amts.append(None)
        else:
            amts.append(q2(D(q.replace(",", "")) * D(p.replace(",", "").replace("$", ""))))
    sub = sum((a for a in amts if a is not None), D(0))
    gst = q2(sub * D("0.1")) if gst_on else D(0)
    return amts, sub, gst, sub + gst


def group_quote(env, R, pages):
    if "quote-template" not in pages:
        return
    W = "quote"
    clock = datetime(2026, 10, 24, 10, 0, tzinfo=timezone(timedelta(hours=10)))
    s = open_clean(env, "quote-template", clock=clock)
    page = s.page
    no_page_errors(R, W, "quote-template", s)
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "it starts with three example lines for lawn care (Mowing, Garden, Washing), quantity 1, price blank, total $0.00",
            [(l["d"], l["q"], l["p"], l["amt"]) for l in st["lines"]] == [("Mowing", "1", "", "\u2014"), ("Garden", "1", "", "\u2014"), ("Washing", "1", "", "\u2014")]
            and st["totals"]["total"] == "$0.00", st)
    R.check(W, "the date starts as today's date from the browser clock", page.input_value("#q-date") == "2026-10-24", page.input_value("#q-date"))
    opts = page.evaluate("Array.from(document.querySelectorAll('#q-trade option')).map(o => [o.value, o.textContent])")
    R.check(W, "the trade selector offers lawn care, pressure washing, cleaning and handyman", opts == [[k, v] for k, v in TRADE_LABELS.items()], opts)

    # service names: only the vetted ones, for every trade
    text = env.read("free/quote-template.html")
    block = re.search(r"var TRADES = \{(.*?)\n  \};", text, re.S).group(1)
    found = {k: re.findall(r"'((?:[^'\\]|\\.)*)'", re.search(r"%s: \{[^}]*services: \[([^\]]*)\]" % k, block).group(1)) for k in VETTED}
    R.check(W, "the service names in the page are exactly Kept's own names for each trade, and nothing else", found == VETTED, found)

    # each trade fills its own examples, and the add buttons show its services
    for key, names in VETTED.items():
        page.select_option("#q-trade", key)
        st = page.evaluate(Q_STATE_JS)
        R.check(W, "%s: the example lines are %s and the add buttons are %s plus a blank line" % (TRADE_LABELS[key], names[:3], names),
                [l["d"] for l in st["lines"]] == names[:3] and st["chips"] == ["Add " + n for n in names] + ["Add a blank line"], (st["lines"], st["chips"]))

    # totals: GST on and off, rounding on odd cents, per line and on the subtotal
    cases = [
        [("Mowing", "1", "50")],
        [("a", "3", "0.05")],
        [("a", "1", "0.05"), ("b", "1", "0.05"), ("c", "1", "0.05")],
        [("a", "0.5", "0.05")],
        [("a", "2.5", "33.33")],
        [("a", "1", "0.01")],
        [("a", "5", "0.01")],
        [("a", "1", "0.04"), ("b", "1", "0.05")],
        [("big", "9,999.99", "999,999.99")],
        [("a", "1,000", "1,250.50"), ("b", "0", "50"), ("c", "2", "$19.99")],
        [("a", "1", ""), ("b", "", "5"), ("c", "2", "7.5")],
        [("", "", "")],
        [("x" * 80, "1", "1")],
    ]
    bad = []
    for lines in cases:
        for gst_on in (False, True):
            page.evaluate(Q_SET_JS, {"lines": lines, "gst": gst_on})
            st = page.evaluate(Q_STATE_JS)
            amts, sub, gst, total = quote_oracle(lines, gst_on)
            want_amts = ["\u2014" if a is None else money(a) for a in amts]
            t = st["totals"]
            ok = ([l["amt"] for l in st["lines"]] == want_amts and t["state"] == "ok" and t["total"] == money(total)
                  and t["subVisible"] == gst_on and t["gstVisible"] == gst_on and t["label"] == ("Total including GST" if gst_on else "Total")
                  and (not gst_on or (t["subtotal"] == money(sub) and t["gst"] == money(gst))))
            if not ok:
                bad.append((lines, gst_on, money(total), want_amts, st["totals"], [l["amt"] for l in st["lines"]]))
    R.check(W, "%d line sets x GST on/off: each line is quantity x price to the cent, the GST is a tenth of the subtotal (half a cent up), totals match the decimal oracle" % len(cases), not bad, bad[:2])
    page.evaluate(Q_SET_JS, {"lines": [("a", "3", "0.05")], "gst": True})
    t = page.evaluate(Q_STATE_JS)["totals"]
    R.check(W, "3 x $0.05 = $0.15; GST on $0.15 is 1.5 cents, rounded up to $0.02; total $0.17", (t["subtotal"], t["gst"], t["total"]) == ("$0.15", "$0.02", "$0.17"), t)
    page.evaluate(Q_SET_JS, {"lines": [("a", "1", "0.05"), ("b", "1", "0.05"), ("c", "1", "0.05")], "gst": True})
    t = page.evaluate(Q_STATE_JS)["totals"]
    R.check(W, "three $0.05 lines: GST is worked out once on the $0.15 subtotal ($0.02), not line by line ($0.03)", (t["subtotal"], t["gst"], t["total"]) == ("$0.15", "$0.02", "$0.17"), t)
    page.evaluate(Q_SET_JS, {"lines": [("a", "1", "50")], "gst": False})
    t = page.evaluate(Q_STATE_JS)["totals"]
    R.check(W, "GST off: only Total is shown ($50.00), no subtotal or GST row", (t["total"], t["subVisible"], t["gstVisible"]) == ("$50.00", False, False), t)
    page.check("#q-gst")
    t = page.evaluate(Q_STATE_JS)["totals"]
    R.check(W, "switching GST on with the real checkbox: Subtotal $50.00, GST (10%) $5.00, Total including GST $55.00", (t["subtotal"], t["gst"], t["total"], t["label"]) == ("$50.00", "$5.00", "$55.00", "Total including GST"), t)
    page.uncheck("#q-gst")
    R.check(W, "and off again: Total $50.00", page.evaluate(Q_STATE_JS)["totals"]["total"] == "$50.00")

    # a seeded sweep against the oracle
    rnd = random.Random(2410)
    bad = []
    for _ in range(60):
        n = rnd.randrange(1, 7)
        lines = [("L%d" % i, ("%d.%02d" % (rnd.randrange(0, 40), rnd.randrange(0, 100))) if rnd.random() < .5 else str(rnd.randrange(0, 40)),
                  ("%d.%02d" % (rnd.randrange(0, 900), rnd.randrange(0, 100)))) for i in range(n)]
        gst_on = rnd.random() < .5
        page.evaluate(Q_SET_JS, {"lines": lines, "gst": gst_on})
        st = page.evaluate(Q_STATE_JS)
        amts, sub, gst, total = quote_oracle(lines, gst_on)
        if st["totals"]["total"] != money(total) or [l["amt"] for l in st["lines"]] != [money(a) for a in amts]:
            bad.append((lines, gst_on, money(total), st["totals"]["total"]))
    R.check(W, "60 seeded random quotes (1 to 6 lines, cents, GST on and off) agree with the decimal oracle", not bad, bad[:2])

    # things that are not numbers
    bad_inputs = [
        ([("a", "1", "-5")], "p", "Price must be $0 or more"), ([("a", "1", "abc")], "p", "Price must be an amount"), ([("a", "1", "1.234")], "p", "at most two digits"),
        ([("a", "1", "1,000,000")], "p", "Price is too large"), ([("a", "-1", "5")], "q", "Quantity must be 0 or more"), ([("a", "abc", "5")], "q", "Quantity must be a number"),
        ([("a", "1.234", "5")], "q", "at most two digits"), ([("a", "10,000", "5")], "q", "Quantity is too large"), ([("a", "1", "12,50")], "p", "Price must be an amount"),
        ([("a", "1", "5"), ("b", "x", "5")], "q", "Line 2: Quantity must be a number"),
    ]
    bad = []
    for lines, field, snippet in bad_inputs:
        page.evaluate(Q_SET_JS, {"lines": lines, "gst": True})
        st = page.evaluate(Q_STATE_JS)
        t = st["totals"]
        ok = (t["state"] == "error" and (t["subtotal"], t["gst"], t["total"]) == ("\u2014", "\u2014", "\u2014") and snippet in t["errs"] and "Fix these" in t["errs"]
              and any(l["inv"] == field for l in st["lines"]) and not re.search(r"NaN|Infinity|undefined", json.dumps(st)))
        if not ok:
            bad.append((lines, snippet, t["state"], t["errs"][:80], [l["inv"] for l in st["lines"]]))
    R.check(W, "%d bad entries (negative, text, 3 decimals, too big) flag the box, say what to fix, and show no totals" % len(bad_inputs), not bad, bad[:2])
    page.evaluate(Q_SET_JS, {"lines": [("a", "1", "abc")], "gst": False})
    page.locator("#q-lines tr [data-f=p]").fill("12")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "fixing the entry brings the totals straight back", st["totals"]["state"] == "ok" and st["totals"]["total"] == "$12.00" and st["totals"]["errs"] == "", st["totals"])

    # lines: add, remove, renumber, focus, the limit
    page.reload()
    page.wait_for_load_state("load")
    page.click("#q-chips button:has-text('Add Hedges')")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "Add Hedges adds a fourth line called Hedges (quantity 1) and moves focus to its price",
            [l["d"] for l in st["lines"]] == ["Mowing", "Garden", "Washing", "Hedges"] and st["lines"][3]["q"] == "1" and st["focus"] == "p" and "Line 4 added" in st["status"], st)
    page.click("#q-chips button:has-text('Add a blank line')")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "Add a blank line adds an empty line and focuses its description", st["lines"][4]["d"] == "" and st["focus"] == "d" and len(st["lines"]) == 5, st)
    page.click("#q-lines tr:nth-child(2) [data-f=rm]")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "Remove takes line 2 away, the labels renumber (Remove line 1..4), focus moves to the next line's description, and a status is announced",
            [l["d"] for l in st["lines"]] == ["Mowing", "Washing", "Hedges", ""] and [l["rm"] for l in st["lines"]] == ["Remove line %d" % i for i in range(1, 5)]
            and st["focus"] == "d" and "Line 2 removed" in st["status"], st)
    for _ in range(4):
        page.click("#q-lines tr:first-child [data-f=rm]")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "every line can be removed: the total is $0.00 and focus goes to the add buttons", len(st["lines"]) == 0 and st["totals"]["total"] == "$0.00" and st["focus"] != "BODY", st)
    for _ in range(35):
        page.click("#q-chips button:has-text('Add a blank line')")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "the template holds 30 lines and says so rather than adding a 31st", len(st["lines"]) == 30 and "up to 30 lines" in st["status"], (len(st["lines"]), st["status"]))

    # the trade selector never throws away what was typed
    page.reload()
    page.wait_for_load_state("load")
    page.locator("#q-lines tr:nth-child(1) [data-f=p]").fill("45")
    page.select_option("#q-trade", "cleaning")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "after typing a price, changing the trade keeps your lines, swaps the add buttons to cleaning, and says so",
            [l["d"] for l in st["lines"]] == ["Mowing", "Garden", "Washing"] and st["lines"][0]["p"] == "45" and st["chips"][0] == "Add Regular clean" and "left as they are" in st["note"], st)
    page.click("#q-reset")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "Start again swaps in the cleaning examples (Regular clean, Bond clean, One-off clean) with no prices", [(l["d"], l["p"]) for l in st["lines"]] == [("Regular clean", ""), ("Bond clean", ""), ("One-off clean", "")] and st["note"] == "", st)
    page.select_option("#q-trade", "handyman")
    st = page.evaluate(Q_STATE_JS)
    R.check(W, "with nothing edited since, the next trade change fills the handyman examples straight away", [l["d"] for l in st["lines"]] == ["General handyman", "Day rate", "Flat-pack assembly"], st["lines"])

    # the printable sheet
    page.reload()
    page.wait_for_load_state("load")
    page.fill("#q-from", "Acme Mowing\nABN 12 345 678 901")
    page.fill("#q-to", "Jane Citizen\n1 Test Street")
    page.fill("#q-no", "Q-7")
    page.fill("#q-date", "2026-10-24")
    page.fill("#q-valid", "2026-11-07")
    page.fill("#q-notes", "Pay within 7 days.")
    page.evaluate(Q_SET_JS, {"lines": [("Mowing", "2", "35.50"), ("Hedges", "1", "120")], "gst": True})
    sheet = page.evaluate("""() => { const s = document.getElementById('sheet'); return {text: s.textContent.replace(/\\s+/g, ' ').trim(), shown: getComputedStyle(s).display,
        cells: Array.from(s.querySelectorAll('.s-lines tbody tr')).map(tr => Array.from(tr.children).map(c => c.textContent)),
        tot: Array.from(s.querySelectorAll('.s-totals tr')).map(tr => [tr.children[0].textContent, tr.children[1].textContent]), pre: getComputedStyle(s.querySelector('.s-text')).whiteSpace}; }""")
    R.check(W, "the sheet (built for printing, hidden on screen) carries the business, customer, number, dates, lines, totals and notes",
            sheet["shown"] == "none" and all(x in sheet["text"] for x in ("Quote no. Q-7", "Date: 24 October 2026", "Valid until: 7 November 2026", "Acme Mowing", "ABN 12 345 678 901", "Jane Citizen", "1 Test Street", "Pay within 7 days."))
            and sheet["cells"] == [["Mowing", "2", "$35.50", "$71.00"], ["Hedges", "1", "$120.00", "$120.00"]]
            and sheet["tot"] == [["Subtotal", "$191.00"], ["GST (10%)", "$19.10"], ["Total including GST", "$210.10"]], sheet)
    page.uncheck("#q-gst")
    tot = page.evaluate("Array.from(document.querySelectorAll('#sheet .s-totals tr')).map(tr => [tr.children[0].textContent, tr.children[1].textContent])")
    R.check(W, "with GST off the sheet shows just Total $191.00", tot == [["Total", "$191.00"]], tot)
    page.evaluate("() => { window.__xss = 0; }")
    page.fill("#q-notes", "<img src=x onerror='window.__xss=1'> <script>window.__xss=2</script>")
    page.locator("#q-lines tr:nth-child(1) [data-f=d]").fill("<b>bold</b><img src=x onerror='window.__xss=3'>")
    got = page.evaluate("() => ({xss: window.__xss, imgs: document.querySelectorAll('#sheet img, #q-lines img, #sheet b').length, text: document.getElementById('sheet').textContent})")
    R.check(W, "typed HTML is shown as plain text, never run", got["xss"] == 0 and got["imgs"] == 0 and "<b>bold</b>" in got["text"], got)
    page.click("#q-print")
    R.check(W, "the Print or save as PDF button calls the browser's print", page.evaluate("window.__printed") == 1)
    s.close()


# ---------------------------------------------------------------------------------------------
# print: the A4 stylesheet, with no site chrome
# ---------------------------------------------------------------------------------------------
def pdf_pages(pdf):
    boxes = re.findall(rb"/MediaBox\s*\[\s*0\s+0\s+([0-9.]+)\s+([0-9.]+)\s*\]", pdf)
    count = len(re.findall(rb"/Type\s*/Page(?![a-zA-Z])", pdf))
    return count, [(float(a), float(b)) for a, b in boxes]


def group_print(env, R, pages):
    if "quote-template" not in pages:
        return
    W = "print"
    text = env.read("free/quote-template.html")
    R.check(W, "the stylesheet sets the page to A4", re.search(r"@page\s*\{[^}]*size:\s*A4", text) is not None)
    for scheme in ("light", "dark"):
        s = open_clean(env, "quote-template", scheme=scheme)
        page = s.page
        page.fill("#q-from", "Acme Mowing")
        page.evaluate(Q_SET_JS, {"lines": [("Mowing", "1", "50"), ("Hedges", "2", "30")], "gst": True})
        screen = page.evaluate("() => ({sheet: getComputedStyle(document.getElementById('sheet')).display, header: getComputedStyle(document.querySelector('header')).display})")
        R.check(W, "%s: on screen the printable sheet is hidden and the header shows" % scheme, screen["sheet"] == "none" and screen["header"] != "none", screen)
        if env.browser_name == "chromium" and scheme == "light":
            pdf = page.pdf(prefer_css_page_size=True)
            n, boxes = pdf_pages(pdf)
            R.check(W, "the PDF is one A4 page (595 x 842 points) holding only the quote", n == 1 and len(boxes) >= 1 and all(abs(w - 595.3) < 2 and abs(h - 841.9) < 2 for w, h in boxes), (n, boxes))
            page.evaluate(Q_SET_JS, {"lines": [("L%d long line %s" % (i, "word " * 30), "1", "10") for i in range(30)], "gst": True})
            page.fill("#q-notes", "x" * 400)
            pdf = page.pdf(prefer_css_page_size=True)
            n, boxes = pdf_pages(pdf)
            R.check(W, "30 long lines run onto more A4 pages, every page A4, none cut off", n >= 2 and all(abs(w - 595.3) < 2 and abs(h - 841.9) < 2 for w, h in boxes), (n, boxes))
            page.evaluate(Q_SET_JS, {"lines": [("Mowing", "1", "50"), ("Hedges", "2", "30")], "gst": True})
        page.emulate_media(media="print")
        info = page.evaluate("""() => { const shown = sel => { const e = document.querySelector(sel); return !!e && e.getClientRects().length > 0; };
          const sheet = document.getElementById('sheet');
          return {header: shown('header'), footer: shown('footer'), hero: shown('.hero'), tool: shown('#tool'), faq: shown('#faq'), cta: shown('.cta-final'), skip: shown('.skip'), sheet: shown('#sheet'),
            sections: Array.from(document.querySelectorAll('main > section')).filter(e => e.getClientRects().length > 0).length,
            bg: getComputedStyle(document.body).backgroundColor, fg: getComputedStyle(sheet).color,
            text: sheet.innerText.replace(/\\s+/g, ' ').trim(), wide: sheet.scrollWidth <= sheet.clientWidth + 1,
            cells: Array.from(sheet.querySelectorAll('th, td')).filter(c => { const cs = getComputedStyle(c); return cs.color !== 'rgb(17, 17, 17)' || cs.backgroundColor !== 'rgba(0, 0, 0, 0)'; }).length}; }""")
        R.check(W, "%s: in print the site header and footer, the intro, the tool, the FAQ and the CTA are all hidden" % scheme,
                not any(info[k] for k in ("header", "footer", "hero", "tool", "faq", "cta", "skip")) and info["sections"] == 0, info)
        R.check(W, "%s: in print only the quote shows, on white, in dark text" % scheme,
                info["sheet"] and info["bg"] in ("rgb(255, 255, 255)", "rgba(0, 0, 0, 0)") and info["fg"] == "rgb(17, 17, 17)"
                and "Quote" in info["text"] and "Acme Mowing" in info["text"] and "Total including GST $121.00" in info["text"] and "Get started" not in info["text"] and "Privacy" not in info["text"], info["text"][:200])
        R.check(W, "%s: the quote fits the sheet's width" % scheme, info["wide"])
        R.check(W, "%s: every table cell on the printed quote is plain dark text with no background (not the site's green headings)" % scheme, info["cells"] == 0, info["cells"])
        page.emulate_media(media="null")
        s.close()
    if env.browser_name == "chromium":
        s = open_clean(env, "quote-template")
        page = s.page
        page.evaluate(Q_SET_JS, {"lines": [("W" * 300, "1", "10"), ("Mowing", "1", "10")], "gst": False})
        page.fill("#q-notes", "x" * 400)
        page.fill("#q-to", "y" * 300)
        page.emulate_media(media="print")
        fits = page.evaluate("() => { const s = document.getElementById('sheet'); return s.scrollWidth <= s.clientWidth + 1; }")
        R.check(W, "a 300-character word in a line, the customer box and the notes wraps inside the sheet (no sideways overflow)", fits)
        s.close()


# ---------------------------------------------------------------------------------------------
# things to do on each page: type something, so there is a result (or a mistake) to look at
# ---------------------------------------------------------------------------------------------
MARK = "ZQXMARKER"


def show_result(page, slug):
    """Put the page in a state with a result showing."""
    if slug == "gst-calculator":
        page.fill("#add-amount", "7654.32")
        page.fill("#rem-amount", "8419.75")
    elif slug == "cents-per-km-calculator":
        page.select_option("#km-year", "2025-26")
        page.fill("#km-input", "2514")
    elif slug == "hourly-rate-calculator":
        page.fill("#h-income", "80000")
        page.fill("#h-weeks", "46")
        page.fill("#h-hours", "25")
        page.fill("#h-costs", "20000")
        page.check("#h-gst")
    elif slug == "quote-template":
        page.fill("#q-from", "%s Mowing\nABN 12 345 678 901" % MARK)
        page.fill("#q-to", "%s Customer\n1 Test Street" % MARK)
        page.fill("#q-no", MARK + "-1")
        page.fill("#q-valid", "2026-11-07")
        page.fill("#q-notes", MARK + " notes " + "w" * 70)
        page.evaluate(Q_SET_JS, {"lines": [(MARK + " Mowing", "2", "35.50"), ("w" * 70, "1", "120"), ("Hedges", "1", "99.95")], "gst": True})
    for d in page.query_selector_all("details"):
        d.evaluate("e => { e.open = true; }")


def show_mistake(page, slug):
    """Put the page in a state with an error or a 'does not apply' message showing."""
    if slug == "gst-calculator":
        page.fill("#add-amount", "abc")
        page.fill("#rem-amount", "-5")
    elif slug == "cents-per-km-calculator":
        page.fill("#km-input", "5001")
    elif slug == "hourly-rate-calculator":
        page.fill("#h-income", "0")
        page.fill("#h-weeks", "0")
        page.fill("#h-hours", "0")
        page.fill("#h-costs", "abc")
    elif slug == "quote-template":
        page.evaluate(Q_SET_JS, {"lines": [("a", "x", "1,000,000"), ("b", "-1", "abc")], "gst": True})
    for d in page.query_selector_all("details"):
        d.evaluate("e => { e.open = true; }")


# ---------------------------------------------------------------------------------------------
# net: nothing typed leaves the browser; nothing is stored; nothing is loaded from anywhere unexpected
# ---------------------------------------------------------------------------------------------
STORAGE_JS = """async () => { const o = {local: {}, session: {}, cookie: document.cookie, name: window.name, idb: [], caches: [], href: location.href};
  try { for (let i = 0; i < localStorage.length; i++) { const k = localStorage.key(i); o.local[k] = localStorage.getItem(k); } } catch (e) {}
  try { for (let i = 0; i < sessionStorage.length; i++) { const k = sessionStorage.key(i); o.session[k] = sessionStorage.getItem(k); } } catch (e) {}
  try { if (indexedDB.databases) o.idb = (await indexedDB.databases()).map(d => d.name); } catch (e) {}
  try { o.caches = await caches.keys(); } catch (e) {}
  o.counters = {fetch: window.__fetch, xhr: window.__xhr, beacons: window.__beacons.length, ws: window.__ws};
  return o; }"""
ALLOWED_PATH = re.compile(r"^/(free(/[a-z-]+)?|attribution\.js|fonts/[A-Za-z0-9.-]+\.woff2|icons/[A-Za-z0-9._-]+)$")
ALLOWED_TYPES = {"document", "script", "font", "image"}


def group_net(env, R, pages):
    W = "net"
    for slug in pages:
        label = PAGE_PATH[slug]
        s = env.session()
        page = s.goto(slug)
        loaded = list(s.requests)
        bad_load = [(u, t) for u, m, t, _ in loaded if not (urlsplit(u).netloc == urlsplit(env.base).netloc and ALLOWED_PATH.match(urlsplit(u).path) and t in ALLOWED_TYPES and m == "GET")]
        R.check(W, "%s: loading it asks only for itself, attribution.js, the font and the icons (%d requests)" % (label, len(loaded)), not bad_load and not s.blocked, (bad_load, s.blocked))
        before = len(s.requests)
        show_result(page, slug)
        show_mistake(page, slug)
        show_result(page, slug)
        page.keyboard.press("Tab")
        for sm in page.query_selector_all("summary"):
            sm.click()
        if slug == "quote-template":
            page.click("#q-print")
            page.click("#q-reset")
        dump = page.evaluate(STORAGE_JS)
        after = s.requests[before:]
        R.check(W, "%s: typing, adding lines, opening the FAQ and printing makes no request at all (%d after load)" % (label, len(after)), not after and not s.blocked, (after[:2], s.blocked[:2]))
        c = dump["counters"]
        R.check(W, "%s: the page itself never calls fetch, XHR, sendBeacon or WebSocket" % label, c == {"fetch": 0, "xhr": 0, "beacons": 0, "ws": 0}, c)
        R.check(W, "%s: nothing is stored: no cookies, no session storage, no IndexedDB, no caches, and the only local storage is attribution.js's own kept_attr" % label,
                dump["cookie"] == "" and not dump["session"] and not dump["idb"] and not dump["caches"] and set(dump["local"]) <= {"kept_attr"},
                (dump["cookie"], dump["session"], dump["idb"], dump["caches"], sorted(dump["local"])))
        blob = json.dumps(dump["local"]) + json.dumps(dump["session"]) + dump["cookie"] + dump["name"] + json.dumps([(u, d) for u, m, t, d in s.requests])
        R.check(W, "%s: what was typed (%s and the figures) is nowhere in storage, the window name or any request" % (label, MARK), not any(x in blob for x in (MARK, "7654", "8419", "2514", "35.50")), blob[:200])
        R.check(W, "%s: the address never changes (nothing typed is put in the URL)" % label, dump["href"] == env.base + PAGE_PATH[slug], dump["href"])
        no_page_errors(R, W, label, s)
        s.close()

        # with Meta's own snippet running (its loader served empty): the pixel loader is the only thing off-site
        s = env.session(stub=False, fbevents=True)
        page = s.goto(slug)
        show_result(page, slug)
        ext = sorted(set(u for u, m, t, d in s.requests if urlsplit(u).netloc != urlsplit(env.base).netloc))
        R.check(W, "%s: with the Meta Pixel snippet running, the only off-site request is its fbevents.js loader" % label,
                ext == ["https://connect.facebook.net/en_US/fbevents.js"] and not s.blocked, (ext, s.blocked))
        s.close()


# ---------------------------------------------------------------------------------------------
# layout: no sideways scroll, readable controls
# ---------------------------------------------------------------------------------------------
OVERFLOW_JS = """() => {
  const vw = document.documentElement.clientWidth, bad = [];
  if (document.documentElement.scrollWidth > vw) bad.push(['document scrollWidth', document.documentElement.scrollWidth, vw]);
  if (document.body.scrollWidth > vw) bad.push(['body scrollWidth', document.body.scrollWidth, vw]);
  for (const el of document.body.querySelectorAll('*')) {
    const cs = getComputedStyle(el);
    if (cs.display === 'none' || cs.visibility === 'hidden') continue;
    const r = el.getBoundingClientRect();
    if (r.width === 0 || r.height === 0) continue;
    if (cs.position === 'absolute' && (cs.clip !== 'auto' || r.width <= 1)) continue;
    if (el.closest('.skip, .sr-only')) continue;
    let q = el.parentElement, hiddenAway = false;   // inside something visually hidden by clipping (a table's header row on phones)
    while (q && q !== document.body) { const qs = getComputedStyle(q), qr = q.getBoundingClientRect(); if (qs.position === 'absolute' && qr.width <= 1 && qr.height <= 1) { hiddenAway = true; break; } q = q.parentElement; }
    if (hiddenAway) continue;
    let p = el.parentElement, scrolls = false;
    while (p && p !== document.body) { const o = getComputedStyle(p).overflowX; if (o === 'auto' || o === 'scroll') { scrolls = true; break; } p = p.parentElement; }
    if (scrolls) continue;
    if (r.right > vw + 1 || r.left < -1) bad.push([el.tagName.toLowerCase() + (el.id ? '#' + el.id : '') + (el.className && typeof el.className === 'string' ? '.' + el.className.split(' ')[0] : ''), Math.round(r.left), Math.round(r.right), vw]);
  }
  return bad.slice(0, 8);
}"""
CONTROLS_JS = """() => {
  const bad = [];
  for (const el of document.querySelectorAll('input[type=text], input[type=date], select, textarea')) {
    const cs = getComputedStyle(el), r = el.getBoundingClientRect();
    if (r.width === 0) continue;
    if (parseFloat(cs.fontSize) < 16) bad.push([el.id, 'font ' + cs.fontSize]);
    if (r.height < 44) bad.push([el.id, 'height ' + Math.round(r.height)]);
  }
  for (const el of document.querySelectorAll('button, .btn, summary')) {
    const r = el.getBoundingClientRect();
    if (r.width === 0) continue;
    if (r.height < 38) bad.push([el.textContent.trim().slice(0, 24), 'height ' + Math.round(r.height)]);
  }
  return bad.slice(0, 8);
}"""
SHOTS_DIR = None


def group_layout(env, R, pages):
    W = "layout"
    for slug in pages:
        for scheme in ("light", "dark"):
            for width in (375, 1280):
                label = "%s %s %dpx" % (PAGE_PATH[slug], scheme, width)
                s = env.session(scheme=scheme, width=width, height=900 if width > 400 else 800,
                                clock=datetime(2026, 10, 24, 10, 0, tzinfo=timezone(timedelta(hours=10))))
                page = s.goto(slug)
                bad = page.evaluate(OVERFLOW_JS)
                R.check(W, "%s: no sideways scroll or overflow on load" % label, not bad, bad)
                show_result(page, slug)
                bad = page.evaluate(OVERFLOW_JS)
                R.check(W, "%s: ... with results, long words and the FAQ open" % label, not bad, bad)
                if SHOTS_DIR is not None:
                    page.screenshot(path=str(Path(SHOTS_DIR) / ("%s-%s-%d.png" % (slug or "index", scheme, width))), full_page=True)
                show_mistake(page, slug)
                bad = page.evaluate(OVERFLOW_JS)
                R.check(W, "%s: ... with error messages showing" % label, not bad, bad)
                bad = page.evaluate(CONTROLS_JS)
                R.check(W, "%s: inputs are 16px+ type and 44px+ tall, buttons 38px+" % label, not bad, bad)
                no_page_errors(R, W, label, s)
                s.close()


# ---------------------------------------------------------------------------------------------
# a11y: headings, labels, live regions, landmarks, keyboard, focus, contrast
# ---------------------------------------------------------------------------------------------
LABELS_JS = """() => {
  const out = [];
  for (const el of document.querySelectorAll('input:not([type=hidden]), select, textarea')) {
    let name = '';
    const lb = el.getAttribute('aria-labelledby');
    if (lb) name = lb.split(/\\s+/).map(id => (document.getElementById(id) || {}).textContent || '').join(' ').trim();
    if (!name && el.getAttribute('aria-label')) name = el.getAttribute('aria-label').trim();
    let visible = false;
    const labels = Array.from(el.labels || []);
    if (!name && labels.length) name = labels.map(l => l.textContent).join(' ').replace(/\\s+/g, ' ').trim();
    for (const l of labels) { const r = l.getBoundingClientRect(), cs = getComputedStyle(l); if (r.width > 8 && r.height > 8 && cs.position !== 'absolute') visible = true; }
    const rr = el.getBoundingClientRect();
    out.push({id: el.id, type: el.type, name: name, visible: visible, shown: rr.width > 0, inTable: !!el.closest('.qt'), describedOk: (el.getAttribute('aria-describedby') || '').split(/\\s+/).filter(Boolean).every(id => !!document.getElementById(id))});
  }
  return out;
}"""
HEADINGS_JS = "() => Array.from(document.querySelectorAll('h1,h2,h3,h4,h5,h6')).map(h => [+h.tagName[1], h.textContent.trim()])"
# Contrast is judged on what is actually painted: the text is hidden, the page screenshotted, and every
# line of text is compared with the pixels behind it (so gradients, tints and translucent headers are real).
CONTRAST_COLLECT_JS = """() => {
  if (document.activeElement && document.activeElement.blur) document.activeElement.blur();
  window.scrollTo(0, 0);
  const cv = document.createElement('canvas'); cv.width = cv.height = 1;
  const cx = cv.getContext('2d', {willReadFrequently: true});
  function rgba(css) { cx.clearRect(0, 0, 1, 1); cx.fillStyle = '#000'; cx.fillStyle = css; cx.fillRect(0, 0, 1, 1);
    const d = cx.getImageData(0, 0, 1, 1).data; return [d[0], d[1], d[2], d[3] / 255]; }
  const items = [], docW = document.documentElement.scrollWidth, docH = document.documentElement.scrollHeight;
  const label = el => el.tagName.toLowerCase() + (el.className && typeof el.className === 'string' && el.className.trim() ? '.' + el.className.trim().split(' ')[0] : '');
  const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
  while (walker.nextNode()) {
    const t = walker.currentNode, el = t.parentElement;
    if (!el || !t.textContent.trim()) continue;
    if (el.closest('script, style, noscript, option, .sr-only, .skip, [hidden]')) continue;
    const cs = getComputedStyle(el);
    if (cs.visibility === 'hidden' || cs.display === 'none') continue;
    let clipped = false;
    for (let q = el; q && q !== document.body; q = q.parentElement) { const qs = getComputedStyle(q); if (qs.position === 'absolute' && qs.clip !== 'auto') { clipped = true; break; } }
    if (clipped) continue;
    const size = parseFloat(cs.fontSize), large = size >= 24 || (size >= 18.66 && parseInt(cs.fontWeight, 10) >= 700);
    const range = document.createRange(); range.selectNodeContents(t);
    for (const r of range.getClientRects()) {
      if (r.width < 3 || r.height < 3 || r.right < 0 || r.bottom < 0 || r.left > docW || r.top > docH) continue;
      items.push({kind: 'text', x: r.left + scrollX, y: r.top + scrollY, w: r.width, h: r.height, fg: rgba(cs.color), min: large ? 3 : 4.5, label: label(el) + ' "' + t.textContent.trim().slice(0, 26) + '"'});
    }
  }
  for (const el of document.querySelectorAll('input[type=text], input[type=date], select, textarea')) {
    const cs = getComputedStyle(el), r = el.getBoundingClientRect();
    if (r.width === 0 || r.height === 0) continue;
    const inset = 8, textPart = (el.type === 'date' || el.tagName === 'SELECT') ? 0.6 : 1;
    const box = {x: r.left + scrollX + inset, y: r.top + scrollY + inset, w: Math.max(2, (r.width - 2 * inset) * textPart), h: Math.max(2, r.height - 2 * inset)};
    const what = el.id || el.tagName;
    if (el.value || el.tagName === 'SELECT') items.push(Object.assign({kind: 'text', fg: rgba(cs.color), min: 4.5, label: 'field text ' + what}, box));
    if (el.placeholder && !el.value) items.push(Object.assign({kind: 'text', fg: rgba(getComputedStyle(el, '::placeholder').color), min: 4.5, label: 'placeholder ' + what}, box));
    items.push({kind: 'border', x: r.left + scrollX - 4, y: r.top + scrollY + r.height / 2, w: 2, h: 2, fg: rgba(cs.borderTopColor), min: 3, label: 'field border ' + what});
  }
  const root = getComputedStyle(document.documentElement), focus = rgba(root.getPropertyValue('--focus').trim() || '#000');
  return {items: items, focus: focus, paper: rgba(root.getPropertyValue('--paper').trim()), white: rgba(root.getPropertyValue('--white').trim()), docW: docW, docH: docH};
}"""
CONTRAST_ANALYSE_JS = """async (args) => {
  const img = new Image(); img.src = 'data:image/png;base64,' + args.png; await img.decode();
  const cv = document.createElement('canvas'); cv.width = img.width; cv.height = img.height;
  const cx = cv.getContext('2d', {willReadFrequently: true}); cx.drawImage(img, 0, 0);
  const lum = c => { const f = v => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }; return 0.2126 * f(c[0]) + 0.7152 * f(c[1]) + 0.0722 * f(c[2]); };
  const ratio = (a, b) => { const l1 = lum(a), l2 = lum(b); return (Math.max(l1, l2) + 0.05) / (Math.min(l1, l2) + 0.05); };
  const bad = []; let tested = 0;
  for (const it of args.items) {
    const x = Math.max(0, Math.floor(it.x)), y = Math.max(0, Math.floor(it.y)), w = Math.min(img.width - x, Math.ceil(it.w)), h = Math.min(img.height - y, Math.ceil(it.h));
    if (w < 1 || h < 1) continue;
    const d = cx.getImageData(x, y, w, h).data; let worst = 99, wb = null;
    const stepX = Math.max(1, Math.floor(w / 60)), stepY = Math.max(1, Math.floor(h / 12));
    for (let j = 0; j < h; j += stepY) for (let i = 0; i < w; i += stepX) {
      const k = (j * w + i) * 4, bg = [d[k], d[k + 1], d[k + 2]], a = it.fg[3];
      const f = [it.fg[0] * a + bg[0] * (1 - a), it.fg[1] * a + bg[1] * (1 - a), it.fg[2] * a + bg[2] * (1 - a)];
      const r = ratio(f, bg); if (r < worst) { worst = r; wb = bg; }
    }
    tested++;
    if (worst < it.min) bad.push([it.label, Math.round(worst * 100) / 100, it.min, 'fg ' + it.fg.map(v => Math.round(v * 100) / 100).join(','), 'bg ' + wb.join(',')]);
  }
  for (const [name, c] of [['paper', args.paper], ['white', args.white]]) { const r = ratio(args.focus, c); if (r < 3) bad.push(['focus ring on ' + name, Math.round(r * 100) / 100, 3]); }
  return {tested: tested, bad: bad.slice(0, 10)};
}"""
HIDE_TEXT_CSS = ("*,*::before,*::after{color:transparent!important;-webkit-text-fill-color:transparent!important;text-shadow:none!important;caret-color:transparent!important}"
                 "::placeholder{color:transparent!important;-webkit-text-fill-color:transparent!important}img{visibility:hidden!important}")


def contrast_check(page):
    import base64
    got = page.evaluate(CONTRAST_COLLECT_JS)
    tag = page.add_style_tag(content=HIDE_TEXT_CSS)
    png = page.screenshot(full_page=True)
    tag.evaluate("e => e.remove()")
    return page.evaluate(CONTRAST_ANALYSE_JS, {"png": base64.b64encode(png).decode(), "items": got["items"], "focus": got["focus"], "paper": got["paper"], "white": got["white"]})


FOCUS_STEP_JS = """() => { const e = document.activeElement; if (!e || e === document.body) return null; const cs = getComputedStyle(e);
  return {tag: e.tagName.toLowerCase(), id: e.id, text: (e.textContent || '').trim().slice(0, 30), href: e.getAttribute('href') || '', outline: cs.outlineStyle, width: parseFloat(cs.outlineWidth)}; }"""
LIVE_REGIONS = {
    "gst-calculator": ["add-out", "rem-out"], "cents-per-km-calculator": ["km-out"], "bas-due-dates": ["bas-live"],
    "hourly-rate-calculator": ["h-out"], "quote-template": ["q-out", "q-status"],
}
KEY_CONTROLS = {
    "": [], "gst-calculator": ["add-amount", "rem-amount"], "cents-per-km-calculator": ["km-year", "km-input"], "bas-due-dates": [],
    "hourly-rate-calculator": ["h-income", "h-weeks", "h-hours", "h-costs", "h-gst"],
    "quote-template": ["q-trade", "q-from", "q-to", "q-no", "q-date", "q-valid", "q-reset", "q-gst", "q-notes", "q-print"],
}


def keyboard_checks(R, W, page, slug, label):
    order = []
    for _ in range(110):
        page.keyboard.press("Tab")
        f = page.evaluate(FOCUS_STEP_JS)
        if f is None:
            continue
        order.append(f)
        if f["text"].startswith("Try the demo"):
            break
    ids = []
    for f in order:
        if f["id"] and (not ids or ids[-1] != f["id"]):
            ids.append(f["id"])
    R.check(W, "%s: the first stop is the skip link, and Tab reaches the last button (Try the demo)" % label,
            bool(order) and order[0]["tag"] == "a" and order[0]["href"] == "#main" and order[-1]["text"].startswith("Try the demo"),
            [o["text"] for o in order[:2]] + [order[-1]["text"] if order else None])
    missing = [c for c in KEY_CONTROLS[slug] if c not in ids]
    R.check(W, "%s: the keyboard reaches %s, in page order" % (label, ", ".join(KEY_CONTROLS[slug]) or "the FAQ questions and the links"),
            not missing and [c for c in ids if c in KEY_CONTROLS[slug]] == [c for c in KEY_CONTROLS[slug]], (missing, ids))
    ringed = set(f["id"] or f["text"] for f in order if f["outline"] != "none" and f["width"] >= 2)
    weak = [(f["tag"], f["id"] or f["text"]) for f in order if (f["id"] or f["text"]) not in ringed]
    R.check(W, "%s: every one of the %d stops Tab makes shows a focus ring (outline 2px or more)" % (label, len(order)), not weak, weak[:3])
    summ = page.query_selector("summary")
    if summ:
        summ.focus()
        before = summ.evaluate("e => e.parentElement.open")
        page.keyboard.press("Enter")
        after = summ.evaluate("e => e.parentElement.open")
        page.keyboard.press("Space")
        again = summ.evaluate("e => e.parentElement.open")
        R.check(W, "%s: a FAQ question opens with Enter and closes with Space" % label, (before, after, again) == (False, True, False), (before, after, again))


def group_a11y(env, R, pages):
    W = "a11y"
    for slug in pages:
        label = PAGE_PATH[slug]
        s = env.session(clock=datetime(2026, 10, 24, 10, 0, tzinfo=timezone(timedelta(hours=10))))
        page = s.goto(slug)
        hs = page.evaluate(HEADINGS_JS)
        levels = [h[0] for h in hs]
        R.check(W, "%s: one h1, then headings that never skip a level (%d headings, none empty)" % (label, len(hs)),
                levels.count(1) == 1 and levels[0] == 1 and all(b <= a + 1 for a, b in zip(levels, levels[1:])) and all(h[1] for h in hs), hs)
        for width in (375, 1280):
            page.set_viewport_size({"width": width, "height": 900})
            labels = page.evaluate(LABELS_JS)
            bad = [l for l in labels if not l["name"] or not l["describedOk"]]
            R.check(W, "%s: every one of %d form controls has a label that names it (and its descriptions exist) at %dpx" % (label, len(labels), width), not bad, bad[:2])
            needs_visible = [l for l in labels if l["shown"] and not (l["inTable"] and width > 640) and l["type"] != "checkbox"]
            bad = [l for l in needs_visible if not l["visible"]]
            R.check(W, "%s: each has a label you can see at %dpx (the quote lines use their column headings on wide screens)" % (label, width), not bad, bad[:2])
            chk = [l for l in labels if l["type"] == "checkbox" and l["shown"]]
            R.check(W, "%s: checkboxes sit inside their label text at %dpx" % (label, width), all(l["name"] for l in chk))
        page.set_viewport_size({"width": 1280, "height": 900})
        main_n = page.evaluate("[document.querySelectorAll('main').length, document.querySelectorAll('header').length, document.querySelectorAll('footer').length, document.querySelectorAll('nav').length]")
        skip = page.evaluate("() => { const a = document.querySelector('a.skip'); return a ? [a.getAttribute('href'), !!document.querySelector(a.getAttribute('href'))] : null; }")
        R.check(W, "%s: one main, one header, one footer, a skip link that lands on the main" % label, main_n[:3] == [1, 1, 1] and skip == ["#main", True], (main_n, skip))
        for rid in LIVE_REGIONS.get(slug, []):
            live = page.evaluate("(id) => { const e = document.getElementById(id); return e ? [e.getAttribute('aria-live'), e.getAttribute('role')] : null; }", rid)
            R.check(W, "%s: #%s is a polite live region" % (label, rid), live is not None and live[0] == "polite", live)

        # keyboard: Tab through the page. (Safari's engine does not Tab to links, buttons or summaries unless a browser
        # setting is turned on, so the Tab walk is only run in Chromium.)
        if env.browser_name == "chromium":
            keyboard_checks(R, W, page, slug, label)
        else:
            R.check(W, "%s: keyboard walk skipped in %s (it only Tabs to form fields by default)" % (label, env.browser_name), True)
        s.close()

        # contrast, light and dark, phone and desktop, with results and with mistakes showing
        for scheme in ("light", "dark"):
            for width in (375, 1280):
                for state in ("fresh", "result", "mistake"):
                    s = env.session(scheme=scheme, width=width, clock=datetime(2026, 10, 24, 10, 0, tzinfo=timezone(timedelta(hours=10))))
                    page = s.goto(slug)
                    if state == "result":
                        show_result(page, slug)
                    elif state == "mistake":
                        show_mistake(page, slug)
                    else:
                        for d in page.query_selector_all("details"):
                            d.evaluate("e => { e.open = true; }")
                    res = contrast_check(page)
                    R.check(W, "%s %s %dpx, %s: text contrast 4.5:1 (3:1 for large text), field borders and the focus ring 3:1 (%d texts and fields checked)" % (label, scheme, width, state, res["tested"]),
                            res["tested"] > 8 and not res["bad"], res["bad"][:4])
                    s.close()


# ---------------------------------------------------------------------------------------------
# cta: the app links are the existing ones, and attribution.js decorates them at run time
# ---------------------------------------------------------------------------------------------
def group_cta(env, R, pages):
    W = "cta"
    for slug in pages:
        label = PAGE_PATH[slug]
        init = ("localStorage.setItem('kept_attr', JSON.stringify({utm_source: 'facebook', utm_medium: 'paid_social', utm_campaign: 'lawn_time', "
                "landing: '%s', seen_at: new Date().toISOString()}));" % PAGE_PATH[slug])
        s = env.session(storage_init=init)
        page = s.goto(slug)
        links = page.evaluate("Array.from(document.querySelectorAll('a[href*=\"app.keptsoftware.com.au\"]')).map(a => a.getAttribute('href'))")
        tag = "&utm_source=facebook&utm_medium=paid_social&utm_campaign=lawn_time&kl=" + PAGE_PATH[slug].replace("/", "%2F")
        want = [APP_FREE + tag, APP_FREE + tag, APP_DEMO + tag]
        R.check(W, "%s: attribution.js adds the saved campaign tags after the existing parameters on all three app links (none added by hand)" % label, sorted(links) == sorted(want), links)
        page.evaluate("window.__fbq = []")
        page.click(".cta-final a.btn:not(.btn-ghost)", no_wait_after=True)
        page.wait_for_function("window.__fbq.length > 0")
        ev = page.evaluate("window.__fbq")
        R.check(W, "%s: the CTA's Get started free click tells Meta about a Lead (start_free)" % label, ev and ev[0][:2] == ["track", "Lead"] and ev[0][2].get("content_name") == "start_free", ev)
        s.close()
        # a visitor with nothing saved: the links stay exactly as written
        s = env.session()
        page = s.goto(slug)
        links = page.evaluate("Array.from(document.querySelectorAll('a[href*=\"app.keptsoftware.com.au\"]')).map(a => a.getAttribute('href'))")
        R.check(W, "%s: a visitor with no campaign saved sees the links exactly as written" % label, sorted(links) == sorted([APP_FREE, APP_FREE, APP_DEMO]), links)
        s.close()


# ---------------------------------------------------------------------------------------------
# running it
# ---------------------------------------------------------------------------------------------
def run_groups(env, R, groups, pages):
    for g in GROUPS:
        if g not in groups:
            continue
        R.section(g)
        try:
            globals()["group_" + g](env, R, pages)
        except Exception as e:   # noqa: BLE001  a crash is a failure, not a reason to stop
            R.check(g, "group crashed: %s: %s" % (type(e).__name__, str(e).splitlines()[0] if str(e) else ""), False)
    return R


def launch(p, name):
    return getattr(p, name).launch()


# ---------------------------------------------------------------------------------------------
# selftest: break the pages on purpose and make sure the suite notices every time
# ---------------------------------------------------------------------------------------------
def M(name, slug, old, new, groups, count=1, pages=None):
    return dict(name=name, slug=slug, old=old, new=new, groups=groups, count=count, pages=pages)


PAD = "<!-- " + "x" * 1200 + " -->"
MUTATIONS = [
    # --- GST calculator
    M("GST: half a cent rounds down instead of up", "gst-calculator", "Math.floor((cents + 5) / 10)", "Math.floor((cents + 4) / 10)", ["static", "gst"]),
    M("GST: the cents are cut off instead of rounded", "gst-calculator", "Math.floor((cents + 5) / 10)", "Math.floor(cents / 10)", ["gst"]),
    M("GST: taking GST out divides by 10 instead of 11", "gst-calculator", "Math.floor((2 * cents + 11) / 22)", "Math.floor((2 * cents + 10) / 20)", ["gst"]),
    M("GST: taking GST out rounds down", "gst-calculator", "Math.floor((2 * cents + 11) / 22)", "Math.floor(cents / 11)", ["gst"]),
    M("GST: an amount like 19.995 is silently cut to 19.99", "gst-calculator", "if (frac.length > 2) return { ok: false, reason: 'decimals' };", "", ["gst"]),
    M("GST: no upper limit on the amount", "gst-calculator", "if (cents > MAX_CENTS) return { ok: false, reason: 'large' };", "", ["gst"]),
    M("GST: the error message for a negative amount is lost", "gst-calculator", "if (/^[-\\u2212(]/.test(s)) return { ok: false, reason: 'negative' };", "", ["gst"]),
    # --- cents per kilometre
    M("km: 5,000 km itself is refused (off by one below)", "cents-per-km-calculator", "p.ok && p.units <= MAX_KM100", "p.ok && p.units < MAX_KM100", ["km"]),
    M("km: 5,001 km is accepted (off by one above)", "cents-per-km-calculator", "var MAX_KM100 = 500000;", "var MAX_KM100 = 500100;", ["km"]),
    M("km: a figure is given above 5,000 km", "cents-per-km-calculator", "if (p.ok && p.units <= MAX_KM100) {", "if (p.ok) {", ["km"]),
    M("km: 2025-26 uses the 2026-27 rate", "cents-per-km-calculator", "'2025-26': 88", "'2025-26': 91", ["km"]),
    M("km: 2024-25 uses an old rate", "cents-per-km-calculator", "'2024-25': 88", "'2024-25': 85", ["km"]),
    M("km: 2026-27 uses the 2025-26 rate", "cents-per-km-calculator", "'2026-27': 91", "'2026-27': 88", ["km"]),
    M("km: the deduction is cut instead of rounded", "cents-per-km-calculator", "Math.floor((km100 * rate + 50) / 100)", "Math.floor((km100 * rate) / 100)", ["km"]),
    M("km: the over-5,000 message no longer says to ask an accountant", "cents-per-km-calculator", "ask your accountant which one suits you", "pick another method", ["static", "km"]),
    M("km: the year list shows the wrong rate", "cents-per-km-calculator", "2026-27: 91 cents per km", "2026-27: 90 cents per km", ["static", "km"]),
    # --- BAS due dates
    M("BAS: Quarter 3 is due on 29 April instead of 28 April", "bas-due-dates", 'data-due="2027-04-28"', 'data-due="2027-04-29"', ["bas"]),
    M("BAS: the table shows the wrong day for Quarter 3", "bas-due-dates", "Wednesday 28 April 2027", "Thursday 29 April 2027", ["bas"]),
    M("BAS: Quarter 2 is taken to be 27 February", "bas-due-dates", 'data-due="2027-02-28"', 'data-due="2027-02-27"', ["bas"]),
    M("BAS: December's monthly date is the 22nd", "bas-due-dates", 'data-due="2026-12-21"', 'data-due="2026-12-22"', ["bas"]),
    M("BAS: a Saturday moves to Sunday, not Monday", "bas-due-dates", "return w === 6 ? ms + 2 * DAY : (w === 0 ? ms + DAY : ms);", "return w === 6 ? ms + DAY : (w === 0 ? ms + DAY : ms);", ["bas"]),
    M("BAS: no weekend rule at all", "bas-due-dates", "return w === 6 ? ms + 2 * DAY : (w === 0 ? ms + DAY : ms);", "return ms;", ["bas"]),
    M("BAS: on the due date it already shows the next one", "bas-due-dates", "if (!next && r.eff >= today) next = r;", "if (!next && r.eff > today) next = r;", ["bas"]),
    M("BAS: today is the UTC date, not the Australian date", "bas-due-dates", "{ timeZone: zone,", "{ timeZone: 'UTC',", ["bas"]),
    M("BAS: the visitor's own Australian time zone is ignored", "bas-due-dates", "if (own && /^Australia\\//.test(own)) zone = own;", "", ["bas"]),
    M("BAS: nothing handles the last date having passed", "bas-due-dates", "if (!next) {", "if (false) {", ["bas"]),
    M("BAS: the online-lodgment wording is changed", "bas-due-dates", "may be eligible for an extra 2 weeks", "are entitled to an extra 2 weeks", ["static", "bas"], count=None),
    M("BAS: the ATO date is wrong on the page", "bas-due-dates", "(page updated 17 September 2026)", "(page updated 17 September 2025)", ["static"]),
    # --- hourly rate
    M("hourly: the GST switch does nothing", "hourly-rate-calculator", "var withGst = gstBox.checked;", "var withGst = false;", ["hourly"]),
    M("hourly: the GST switch works backwards", "hourly-rate-calculator", "var withGst = gstBox.checked;", "var withGst = !gstBox.checked;", ["hourly"]),
    M("hourly: zero billable hours is not guarded", "hourly-rate-calculator", "(u < 10 || u > 1680)", "(u > 1680)", ["hourly"]),
    M("hourly: zero weeks is not guarded", "hourly-rate-calculator", "(u < 1 || u > 52)", "(u > 52)", ["hourly"]),
    M("hourly: the rate is cut instead of rounded", "hourly-rate-calculator", "Math.floor((20 * totalCents + hoursTenths) / (2 * hoursTenths))", "Math.floor((10 * totalCents) / hoursTenths)", ["hourly"]),
    M("hourly: the GST on the rate is cut instead of rounded", "hourly-rate-calculator", "return Math.floor((cents + 5) / 10);", "return Math.floor(cents / 10);", ["hourly"]),
    M("hourly: huge amounts are accepted", "hourly-rate-calculator", "} else if (f.money && p.units > MAX_MONEY) {", "} else if (false) {", ["hourly"]),
    M("hourly: an income of $0 is accepted", "hourly-rate-calculator", "return u < 1 ? 'Enter the income", "return u < 0 ? 'Enter the income", ["hourly"]),
    # --- quote template
    M("quote: the GST switch does nothing", "quote-template", "var on = gstBox.checked, gst = on ? Math.floor((sub + 5) / 10) : 0;", "var on = false, gst = 0;", ["quote"]),
    M("quote: GST is cut instead of rounded", "quote-template", "Math.floor((sub + 5) / 10)", "Math.floor(sub / 10)", ["quote"]),
    M("quote: a line's amount is cut instead of rounded", "quote-template", "Math.floor((row.qty * row.price + 50) / 100)", "Math.floor((row.qty * row.price) / 100)", ["quote"]),
    M("quote: the subtotal drops the last line", "quote-template", "data.forEach(function (r) { if (r.amount !== null) sub += r.amount; });", "data.slice(0, -1).forEach(function (r) { if (r.amount !== null) sub += r.amount; });", ["quote"]),
    M("quote: a service name that is not Kept's", "quote-template", "services: ['Mowing', 'Garden',", "services: ['Mowing and edging', 'Garden',", ["quote"]),
    M("quote: changing the trade throws away typed lines", "quote-template", "if (!dirty) {", "if (true) {", ["quote"]),
    M("quote: typed text is put in as HTML", "quote-template", "if (text !== undefined) n.textContent = text;", "if (text !== undefined) n.innerHTML = text;", ["quote"]),
    M("quote: no limit on the number of lines", "quote-template", "if (body.children.length >= MAX_LINES) {", "if (false) {", ["quote"]),
    M("quote: printing still shows the site header", "quote-template", ".skip,header,footer,main>section{display:none!important}", ".skip,footer,main>section{display:none!important}", ["print"]),
    M("quote: printing still shows the site footer", "quote-template", ".skip,header,footer,main>section{display:none!important}", ".skip,header,main>section{display:none!important}", ["print"]),
    M("quote: printing still shows the CTA and FAQ", "quote-template", ".skip,header,footer,main>section{display:none!important}", ".skip,header,footer{display:none!important}", ["print"]),
    M("quote: the page size is Letter, not A4", "quote-template", "@page{size:A4;margin:14mm}", "@page{size:letter;margin:14mm}", ["static", "print"]),
    M("quote: what is typed is sent to a server", "quote-template", "function renderSheet() {", "function renderSheet() { try { fetch('/leak?x=' + encodeURIComponent($('q-from').value)); } catch (e) {}", ["static", "net"]),
    M("quote: what is typed is kept in local storage", "quote-template", "function renderSheet() {", "function renderSheet() { try { localStorage.setItem('q', $('q-from').value); } catch (e) {}", ["static", "net"]),
    M("quote: what is typed is put in the address bar", "quote-template", "function renderSheet() {", "function renderSheet() { try { history.replaceState(null, '', '#' + encodeURIComponent($('q-from').value)); } catch (e) {}", ["net"]),
    M("quote: a script error on load", "quote-template", "(function () {\n  'use strict';\n\n  // The service names", "(function () {\n  'use strict';\n  notDefinedAnywhere();\n\n  // The service names", ["quote"]),
    M("quote: the Print button does nothing", "quote-template", "    renderSheet();\n    window.print();", "    renderSheet();", ["quote"]),
    # --- things every page must keep
    M("all: the Meta Pixel init line is missing", "gst-calculator", re.compile(r"  fbq\('init', '\d+'\);\n"), "", ["static"]),
    M("all: the pixel carries the ad account number, not the pixel's own ID", "cents-per-km-calculator", re.compile(r"fbq\('init', '\d+'\)"), "fbq('init', '1049765071100614')", ["static"]),
    M("all: attribution.js is missing", "cents-per-km-calculator", '  <script src="/attribution.js" defer></script>\n', "", ["static", "cta"]),
    M("all: attribution.js is loaded in the wrong place", "bas-due-dates", '<script src="/attribution.js" defer></script>\n<meta charset="UTF-8">', '<meta charset="UTF-8">\n<script src="/attribution.js" defer></script>', ["static"]),
    M("all: a held word (Pay now) in the intro", "cents-per-km-calculator", "The ATO cents per kilometre rate is 91 cents", "Pay now: the ATO cents per kilometre rate is 91 cents", ["static"]),
    M("all: a held word (automatically) in the call to action", "gst-calculator", "Kept works out the GST for you.", "Kept works out the GST for you automatically.", ["static"]),
    M("all: a price the pages must not state", "hourly-rate-calculator", "Free plan, no time limit.", "From $35/mo.", ["static"], count=None),
    M("all: the charset tag is pushed past 1024 bytes", "quote-template", '<meta charset="UTF-8">', PAD + '<meta charset="UTF-8">', ["static"]),
    M("all: a second h1", "gst-calculator", '<h2 class="sr-only">The calculators</h2>', "<h1>Another heading</h1>", ["static", "a11y"]),
    M("all: a heading level is skipped", "hourly-rate-calculator", "<h2 class=\"sr-only\">The calculator</h2>", "<h4 class=\"sr-only\">The calculator</h4>", ["static", "a11y"]),
    M("all: a script from another site", "bas-due-dates", "</body>", '<script src="https://example.com/x.js"></script></body>', ["static", "net"]),
    M("all: an ATO source with the wrong date", "cents-per-km-calculator", "(page updated 12 August 2026)", "(page updated 12 August 2025)", ["static"]),
    M("all: a call to action link with a campaign tag typed in by hand", "hourly-rate-calculator", 'href="https://app.keptsoftware.com.au/?demo=1"', 'href="https://app.keptsoftware.com.au/?demo=1&utm_source=x"', ["static", "cta"]),
    M("all: the FAQ answer in the structured data no longer matches the page", "gst-calculator", "Add a tenth of the price.", "Add a quarter of the price.", ["static"]),
    M("all: an input with no label", "cents-per-km-calculator", '<label for="km-input">Work-related kilometres for the year</label>', "<span>Work-related kilometres for the year</span>", ["a11y"]),
    M("all: a text box with no visible label on a phone", "gst-calculator", '<label for="add-amount">Price before GST</label>', '<label for="add-amount" class="sr-only">Price before GST</label>', ["a11y"]),
    M("all: the results are not announced (no aria-live)", "cents-per-km-calculator", 'id="km-out" aria-live="polite"', 'id="km-out"', ["a11y"]),
    M("all: the focus ring is switched off", "hourly-rate-calculator", "</style>", "*:focus-visible{outline:none!important}\n</style>", ["a11y"]),
    M("all: text too pale to read", "cents-per-km-calculator", ".hint{font-size:.85rem;color:var(--ink-soft);margin-top:6px}", ".hint{font-size:.85rem;color:#b9c1bc;margin-top:6px}", ["a11y"]),
    M("all: pale text in dark mode only", "gst-calculator", "--err:#FF9E9E;", "--err:#5a2a2a;", ["a11y"]),
    M("all: sideways scroll on a phone", "cents-per-km-calculator", "</style>", ".tool{min-width:560px}\n</style>", ["layout"]),
    M("all: a long word breaks the quote's layout", "quote-template", ".result{border-radius:var(--radius);padding:18px 20px;", ".result{white-space:nowrap;border-radius:var(--radius);padding:18px 20px;", ["layout"]),
    M("all: a tag left open", "gst-calculator", '<section id="faq">\n  <div class="wrap narrow">', '<section id="faq">\n  <div class="wrap narrow"><div>', ["static"]),
    M("all: two elements with the same id", "gst-calculator", '<section id="faq">', '<section id="tool">', ["static"]),
    M("all: a broken internal link", "hourly-rate-calculator", 'href="/free/gst-calculator"', 'href="/free/gst-calc"', ["static"]),
    M("all: two pages share a title", "bas-due-dates", "<title>BAS Due Dates 2026-27: Quarterly and Monthly | Kept</title>", "<title>GST Calculator Australia: Add or Remove 10% GST | Kept</title>", ["static"], pages=["bas-due-dates", "gst-calculator"]),
    M("all: the index no longer lists the BAS tool", "", 'href="/free/bas-due-dates"', 'href="/free/bas-dates"', ["static"]),
]


def selftest(args):
    mutations = [m for m in MUTATIONS if args.grep.lower() in m["name"].lower()]
    if not mutations:
        print("no deliberate break matches %r" % args.grep)
        return 1
    tmp = Path(tempfile.mkdtemp(prefix="free-pages-selftest-"))
    root = tmp / "site"
    shutil.copytree(SITE, root, ignore=shutil.ignore_patterns(".git", "node_modules", "videos", "images", "tools", "card", "clean", "wash", "handyman", "lawn-care"))
    print("selftest: working on a temporary copy in %s" % root, flush=True)
    site = Site(root)
    missed, baseline_bad = [], []
    try:
        with sync_playwright() as p:
            browser = launch(p, args.browser)
            env = Env(browser, site, args.browser)
            # the suite must pass on the untouched copy for each page and group it is about to be asked about
            wanted = {}
            for m in mutations:
                wanted.setdefault(m["slug"], set()).update(m["groups"])
            for slug, groups in sorted(wanted.items()):
                R = run_groups(env, Results(echo=False), groups, [slug])
                state = "clean" if not R.failed else "NOT CLEAN"
                print("baseline %-26s groups %-34s %d checks, %s" % (PAGE_PATH[slug], ",".join(sorted(groups)), len(R.rows), state), flush=True)
                if R.failed:
                    baseline_bad.append((slug, [(r[0], r[1], r[3]) for r in R.failed][:2]))
            if baseline_bad:
                print("SELFTEST FAILED: the suite is not clean on the untouched pages, so the results below would mean nothing: %s" % baseline_bad)
                return 1
            for m in mutations:
                path = root / ("free/index.html" if m["slug"] == "" else "free/%s.html" % m["slug"])
                original = path.read_text(encoding="utf-8")
                if hasattr(m["old"], "search"):
                    found = m["old"].search(original) is not None
                else:
                    found = m["old"] in original
                if not found:
                    print("SELF-TEST BROKEN   %-70s the text to break was not found" % m["name"])
                    missed.append(m["name"] + " (target not found)")
                    continue
                if hasattr(m["old"], "sub"):
                    broken = m["old"].sub(m["new"], original, count=1)
                else:
                    broken = original.replace(m["old"], m["new"]) if m["count"] is None else original.replace(m["old"], m["new"], m["count"])
                assert broken != original, m["name"]
                path.write_text(broken, encoding="utf-8")
                try:
                    R = run_groups(env, Results(echo=False), set(m["groups"]), m["pages"] or [m["slug"]])
                finally:
                    path.write_text(original, encoding="utf-8")
                if R.failed:
                    first = R.failed[0]
                    print("CAUGHT      %-70s by [%s] %s" % (m["name"], first[0], first[1][:90]), flush=True)
                else:
                    print("NOT CAUGHT  %-70s" % m["name"], flush=True)
                    missed.append(m["name"])
            browser.close()
    finally:
        site.close()
        shutil.rmtree(tmp, ignore_errors=True)
    if missed:
        print("\nSELFTEST FAILED: %d of %d deliberate breaks were not caught:\n  - %s" % (len(missed), len(mutations), "\n  - ".join(missed)))
        return 1
    print("\nSELFTEST OK: all %d deliberate breaks were caught" % len(mutations))
    return 0


def main():
    global SHOTS_DIR
    ap = argparse.ArgumentParser(description="Tests for the free tool pages")
    ap.add_argument("--selftest", action="store_true", help="break the pages on purpose and check the suite notices")
    ap.add_argument("--only", default="", help="comma-separated groups: " + ",".join(GROUPS))
    ap.add_argument("--page", default="", help="one page: index, " + ", ".join(SLUGS))
    ap.add_argument("--browser", default="chromium", choices=["chromium", "webkit"])
    ap.add_argument("--shots", default="", help="save a screenshot of every page into this folder")
    ap.add_argument("--grep", default="", help="with --selftest: only the deliberate breaks whose name contains this text")
    args = ap.parse_args()
    if args.selftest:
        sys.exit(selftest(args))
    groups = [g for g in args.only.split(",") if g] or GROUPS
    unknown = [g for g in groups if g not in GROUPS]
    if unknown:
        ap.error("unknown group(s): %s" % ", ".join(unknown))
    pages = ALL_PAGES
    if args.page:
        pages = ["" if args.page == "index" else args.page]
        if pages[0] not in ALL_PAGES:
            ap.error("unknown page %r" % args.page)
    if args.shots:
        SHOTS_DIR = args.shots
        Path(SHOTS_DIR).mkdir(parents=True, exist_ok=True)
    site = Site(SITE)
    R = Results()
    try:
        with sync_playwright() as p:
            browser = launch(p, args.browser)
            env = Env(browser, site, args.browser)
            run_groups(env, R, set(groups), pages)
            browser.close()
    finally:
        site.close()
    per = {}
    for g, _, ok, _ in R.rows:
        c = per.setdefault(g, [0, 0])
        c[0] += 1
        c[1] += (not ok)
    print("\n%s" % "  ".join("%s %d%s" % (g, per[g][0], " (%d FAILED)" % per[g][1] if per[g][1] else "") for g in GROUPS if g in per))
    print("%d checks, %d failed" % (len(R.rows), len(R.failed)))
    sys.exit(1 if R.failed else 0)


if __name__ == "__main__":
    main()
