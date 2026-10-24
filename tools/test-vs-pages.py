#!/usr/bin/env python3
"""Checks for the two comparison pages vs-sortscape.html and vs-fergus.html (and their source table).

Run it with the app repo's Python, which has Playwright and a cached headless Chromium
(there is no Node on this machine):

  PY="/Users/elliotlangham/Documents/Lawn envy revamp/jobs-app/tools/demo-capture/.venv/bin/python"
  "$PY" tools/test-vs-pages.py                 # everything; PASS/FAIL per check, exit 1 on any FAIL
  "$PY" tools/test-vs-pages.py --static        # only the checks that need no browser (plain python3 works too)
  "$PY" tools/test-vs-pages.py --only head,figures
  "$PY" tools/test-vs-pages.py --selftest      # proves the suite can fail: breaks a temp copy of the pages
                                               # (and of tools/vs-sources.json) on purpose, once or more
                                               # for every check, and confirms the suite goes red each time

What it covers, per page:
  head        charset in the first 1024 bytes, one <title>, one meta description, canonical, og tags,
              icons, and the whole top of the file (doctype, Meta Pixel block, attribution tag, viewport)
              identical to the sibling pages
  jsonld      FAQPage structured data parses and says exactly what the visible FAQ says
  pixel       the Meta Pixel block and /attribution.js, right after "End Meta Pixel Code", exactly once
  links       every link to the app is in one of the forms the sibling pages use (the attribution script
              adds the campaign tags at run time, so none are written by hand); no other external links
  copy        no "tax invoice"; none of the held words (Pay now, automatically, set and forget, encryption,
              AI, testimonial, 3 months free, free forever, founding offer ...); no superlatives, "better
              than", disparagement or unsourced negatives; route optimisation is never offered for Kept
              without "Team plan and above"
  figures     every number on a page is either one of the Kept figures the sibling pages already state or a
              competitor figure listed in tools/vs-sources.json (and the other way round); Kept's only
              prices are $35 and $229+
  sources     tools/vs-sources.json: sound entries, official or review-site URLs, dates not in the future,
              every figure present in its quoted wording, every page_text fragment present on its page,
              every review site named on a page has a source
  table       header row, data-labels (the phone cards read them), first row highlighted, the pricing-note
              sentence with the month; every competitor cell is covered by sourced fragments and every
              Kept cell by the vetted Kept claims
  structure   <style> block, header, footer, final call to action and section order the same as the siblings
  hscroll     no horizontal scroll at 375 px and 1280 px
  cards       on a phone the table turns into cards (labels from data-label); on desktop it stays a table
  contrast    every piece of text has contrast >= 4.5 against what is really drawn behind it, in dark and
              in light mode (measured from a screenshot taken with the text made transparent)
  errors      no uncaught page errors and no failed request to the site's own files

How the browser checks work: the site folder is served from a local threaded http.server on a free port.
Every request to anywhere else (Facebook, the app, ...) is aborted. Python 3.9 compatible.
"""
import argparse
import base64
import functools
import html as htmllib
import http.server
import json
import re
import shutil
import sys
import tempfile
import threading
import traceback
from datetime import date, datetime
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit

SITE = Path(__file__).resolve().parent.parent
SIBLING = "vs-yardbook.html"
SOURCES_REL = "tools/vs-sources.json"
SITE_BASE = "https://www.keptsoftware.com.au/"

APP_ROOT = "https://app.keptsoftware.com.au/"
APP_LAWN = "https://app.keptsoftware.com.au/?industry=lawn_care"
APP_DEMO = "https://app.keptsoftware.com.au/?demo=1"

PAGES = {
    "vs-sortscape.html": {
        "name": "SortScape", "slug": "vs-sortscape",
        "app": {APP_LAWN, APP_DEMO},
        "hosts": {"sortscape.com.au", "www.capterra.com", "apps.xero.com"},
        "review_sites": {"Capterra": "capterra.com", "Xero App Store": "apps.xero.com"},
    },
    "vs-fergus.html": {
        "name": "Fergus", "slug": "vs-fergus",
        "app": {APP_ROOT, APP_DEMO},
        "hosts": {"fergus.com", "www.capterra.com", "apps.xero.com", "www.trustpilot.com"},
        "review_sites": {"Capterra": "capterra.com", "Xero App Store": "apps.xero.com", "Trustpilot": "trustpilot.com"},
    },
}
OTHER_HREFS = {"/", "/#features", "/#compare", "/#pricing", "/#faq", "/privacy", "/terms",
               "mailto:support@keptsoftware.com.au", "https://www.lawnenvyaustralia.com"}

MONTHS = "January|February|March|April|May|June|July|August|September|October|November|December"
DATE_RE = re.compile(r"\b\d{1,2} (?:%s) 20\d\d\b|\b(?:%s) 20\d\d\b" % (MONTHS, MONTHS))
NUM_RE = re.compile(r"\d[\d,]*(?:\.\d+)?")

# Kept's own figures that the sibling pages and the homepage already state. Anything else numeric on a page
# must be a competitor figure listed in vs-sources.json.
KEPT_FIGURES = [
    re.compile(r"\$35(?!\d)"), re.compile(r"\$229\+?"),
    re.compile(r"\b15 clients\b"), re.compile(r"\b15 jobs/quotes\b"),
    re.compile(r"\b20\+"), re.compile(r"\bover 20 other trades\b"),
    re.compile(r"\(1, 2–4, 5–10, 11\+\)"), re.compile(r"\(1 person, 2–4, 5–10, 11\+\)"),
    re.compile(r"\b2–4\b"), re.compile(r"\b5–10\b"), re.compile(r"\b11\+"), re.compile(r"\b1 person\b"),
    re.compile(r"\bout of 5\b"),
]
KEPT_DOLLARS = {"$35", "$229"}

# Words the vetted-claims list says never to use (APP-CLAIMS.md "Do NOT say") plus the lead's list.
HELD = [
    ("tax invoice", re.compile(r"tax[\s-]*invoices?", re.I)),
    ("Pay now", re.compile(r"\bpay[\s-]*now\b", re.I)),
    ("automatically", re.compile(r"\bautomatically\b", re.I)),
    ("set and forget", re.compile(r"\bset[\s-]*(it[\s-]*)?(and|&)[\s-]*forget\b", re.I)),
    ("encryption", re.compile(r"\bencrypt\w*", re.I)),
    ("AI", re.compile(r"\bAI\b")),
    ("testimonial", re.compile(r"\btestimonials?\b", re.I)),
    ("3 months free", re.compile(r"\b(?:3|three)\s*months?\s*free\b", re.I)),
    ("free forever", re.compile(r"\bfree[\s-]*forever\b|\bforever[\s-]*free\b", re.I)),
    ("founding offer", re.compile(r"\bfounding\b|\bfirst 100\b", re.I)),
    ("autopilot", re.compile(r"\bauto-?pilot\b", re.I)),
    ("bank-grade", re.compile(r"\bbank[\s-]*grade\b", re.I)),
]
TONE = [
    ("superlative", re.compile(r"\b(best|cheapest|easiest|fastest|simplest|unbeatable|number one|#1|world[\s-]class|market[\s-]leading|industry[\s-]leading|leading)\b", re.I)),
    ("'better/worse than'", re.compile(r"\b(better|worse|superior|inferior)\s+than\b|\boutperforms?\b|\bbeats?\b", re.I)),
    ("disparagement", re.compile(r"\b(terrible|awful|rubbish|rip-?off|scam|useless|dreadful|appalling|clunky|outdated|unreliable|overpriced|poor)\b", re.I)),
    ("unsourced negative about a competitor", re.compile(r"\b(lacks?|lacking|doesn'?t (?:have|offer|support|include)|does not (?:have|offer|support|include)|missing|not available)\b", re.I)),
    ("absolute", re.compile(r"\b(guarantee[sd]?|always|never)\b", re.I)),
]
CONNECT = {"and", "or", "on", "with", "the", "a", "for", "of", "to", "by", "from", "in"}
STALE_DAYS = 90


# ---------------------------------------------------------------------------------------------
# A tiny DOM, enough for these pages
# ---------------------------------------------------------------------------------------------
VOID = {"meta", "link", "img", "br", "hr", "input", "source", "area", "base", "col", "embed", "param", "track", "wbr"}


class Node(object):
    __slots__ = ("tag", "attrs", "kids", "parent")

    def __init__(self, tag, attrs=None, parent=None):
        self.tag, self.attrs, self.kids, self.parent = tag, attrs or {}, [], parent

    def classes(self):
        return (self.attrs.get("class") or "").split()


class Builder(HTMLParser):
    def __init__(self):
        HTMLParser.__init__(self, convert_charrefs=True)
        self.root = Node("#root")
        self.cur = self.root

    def handle_starttag(self, tag, attrs):
        n = Node(tag, dict((k, v if v is not None else "") for k, v in attrs), self.cur)
        self.cur.kids.append(n)
        if tag not in VOID:
            self.cur = n

    def handle_startendtag(self, tag, attrs):
        n = Node(tag, dict((k, v if v is not None else "") for k, v in attrs), self.cur)
        self.cur.kids.append(n)

    def handle_endtag(self, tag):
        n = self.cur
        while n is not self.root and n.tag != tag:
            n = n.parent
        if n is not self.root:
            self.cur = n.parent

    def handle_data(self, data):
        self.cur.kids.append(data)


def parse(text):
    b = Builder()
    b.feed(text)
    b.close()
    return b.root


def walk(n):
    for k in n.kids:
        if isinstance(k, str):
            continue
        yield k
        for x in walk(k):
            yield x


def find_all(n, tag=None, cls=None, **attrs):
    out = []
    for x in walk(n):
        if tag and x.tag != tag:
            continue
        if cls and cls not in x.classes():
            continue
        if any(x.attrs.get(k.replace("_", "-")) != v for k, v in attrs.items()):
            continue
        out.append(x)
    return out


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def node_text(n, sep=""):
    out = []

    def rec(x):
        for k in x.kids:
            if isinstance(k, str):
                out.append(k)
            elif k.tag not in ("script", "style"):
                rec(k)
    rec(n)
    return norm(sep.join(out))


def visible_text(root):
    out = []

    def rec(x):
        for k in x.kids:
            if isinstance(k, str):
                out.append(k)
            elif k.tag not in ("script", "style", "noscript", "template", "head"):
                rec(k)
    rec(root)
    return norm(" ".join(out))


def numbers(s):
    return [t.replace(",", "") for t in NUM_RE.findall(s)]


def figure_tokens(s):
    """Numbers left on a page after the Kept figures, dates and 'out of 5' are taken out."""
    t = DATE_RE.sub(" ", s)
    for p in KEPT_FIGURES:
        t = p.sub(" ", t)
    return numbers(t)


def uncovered(text, fragments):
    """Words of `text` that are not part of any listed fragment (or a plain connector word)."""
    t = text
    for fr in sorted(set(fragments), key=len, reverse=True):
        if fr:
            t = t.replace(fr, "\x00")
    return [w for w in re.split(r"[\s\x00,;:()]+", t) if w and w.lower() not in CONNECT]


# ---------------------------------------------------------------------------------------------
# Results and the shared context
# ---------------------------------------------------------------------------------------------
class Results(object):
    def __init__(self, echo=True):
        self.rows = []      # (group, name, ok, detail)
        self.warns = []
        self.echo = echo

    def section(self, group, title):
        if self.echo:
            print("\n== %s: %s" % (group, title), flush=True)

    def check(self, group, name, ok, detail=""):
        ok = bool(ok)
        self.rows.append((group, name, ok, detail))
        if self.echo:
            line = "%s  [%s] %s" % ("PASS" if ok else "FAIL", group, name)
            if not ok and detail:
                line += "\n        -> %s" % (detail,)
            print(line, flush=True)

    def warn(self, group, text):
        self.warns.append((group, text))
        if self.echo:
            print("WARN  [%s] %s" % (group, text), flush=True)

    @property
    def failed(self):
        return [r for r in self.rows if not r[2]]

    def failed_groups(self):
        return set(r[0] for r in self.failed)


class NoCache(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        http.server.SimpleHTTPRequestHandler.end_headers(self)

    def log_message(self, *a):
        pass


class Ctx(object):
    def __init__(self, site):
        self.site = Path(site)
        self.srv = None
        self.base = None
        self.pw = None
        self.browser = None

    # files
    def raw(self, f):
        return (self.site / f).read_bytes()

    def text(self, f):
        return self.raw(f).decode("utf-8")

    def dom(self, f):
        return parse(self.text(f))

    def sources(self):
        return json.loads((self.site / SOURCES_REL).read_text(encoding="utf-8"))

    def copy_text(self, f):
        """Everything a reader or a crawler sees: title, meta contents, visible text, JSON-LD strings."""
        t = self.text(f)
        parts = [htmllib.unescape(x) for x in re.findall(r"<title>(.*?)</title>", t, re.S)]
        parts += [htmllib.unescape(x) for x in re.findall(r'<meta (?:name="description"|property="og:(?:title|description)") content="([^"]*)"', t)]
        parts.append(visible_text(self.dom(f)))
        for blob in re.findall(r'<script type="application/ld\+json">(.*?)</script>', t, re.S):
            try:
                parts += [s for s in json_strings(json.loads(blob))]
            except ValueError:
                pass
        return norm(" ".join(parts))

    # browser
    def ensure_browser(self):
        if self.browser:
            return
        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            raise SystemExit("Playwright is not installed for this Python. Use the app repo's venv "
                             "(see the top of this file), or run with --static.")
        handler = functools.partial(NoCache, directory=str(self.site))
        self.srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
        self.base = "http://127.0.0.1:%d" % self.srv.server_address[1]
        threading.Thread(target=self.srv.serve_forever, daemon=True).start()
        self.pw = sync_playwright().start()
        self.browser = self.pw.chromium.launch()

    def new_page(self, width, scheme, height=900):
        self.ensure_browser()
        bctx = self.browser.new_context(viewport={"width": width, "height": height}, color_scheme=scheme, device_scale_factor=1)
        base = self.base
        bctx.route("**/*", lambda route: route.continue_() if route.request.url.startswith(base) else route.abort())
        page = bctx.new_page()
        page.errors, page.bad = [], []
        page.on("pageerror", lambda e: page.errors.append(str(e)))
        page.on("response", lambda r: page.bad.append("%s %s" % (r.status, r.url)) if r.url.startswith(base) and r.status >= 400 else None)
        return bctx, page

    def open(self, f, width, scheme="light"):
        bctx, page = self.new_page(width, scheme)
        page.goto(self.base + "/" + f, wait_until="load")
        page.evaluate("document.fonts.ready.then(function(){return true})")
        page.evaluate("document.querySelectorAll('details').forEach(function(d){d.open=true})")
        return bctx, page

    def close(self):
        try:
            if self.browser:
                self.browser.close()
            if self.pw:
                self.pw.stop()
            if self.srv:
                self.srv.shutdown()
        except Exception:   # noqa: BLE001
            pass
        self.browser = self.pw = self.srv = None


def json_strings(o):
    if isinstance(o, str):
        yield o
    elif isinstance(o, dict):
        for v in o.values():
            for s in json_strings(v):
                yield s
    elif isinstance(o, list):
        for v in o:
            for s in json_strings(v):
                yield s


CHECKS = []   # (group, function, needs_browser)


def check(group, browser=False):
    def deco(fn):
        CHECKS.append((group, fn, browser))
        return fn
    return deco


def sentences(s):
    return [x for x in re.split(r"(?<=[.!?])\s+", s) if x]


# ---------------------------------------------------------------------------------------------
# Static checks
# ---------------------------------------------------------------------------------------------
@check("head")
def check_head(ctx, R):
    R.section("head", "the <head> follows the sibling pages")
    sib = ctx.text(SIBLING)
    for f, cfg in PAGES.items():
        raw = ctx.raw(f)
        text = raw.decode("utf-8")
        i = raw.find(b'<meta charset="UTF-8">')
        R.check("head", "%s: <meta charset> inside the first 1024 bytes" % f, 0 <= i < 1024, "offset %d" % i)
        R.check("head", "%s: <html lang=\"en-AU\">" % f, text.startswith('<!DOCTYPE html>\n<html lang="en-AU">\n<head>'))
        titles = re.findall(r"<title>(.*?)</title>", text, re.S)
        R.check("head", "%s: exactly one <title>" % f, len(titles) == 1 and text.count("<title") == 1, "%d" % text.count("<title"))
        t = htmllib.unescape(titles[0]) if titles else ""
        R.check("head", "%s: title reads 'Kept vs %s — ... | Kept'" % (f, cfg["name"]),
                re.fullmatch(r"Kept vs %s — .{10,60} \| Kept" % re.escape(cfg["name"]), t) is not None, t)
        descs = re.findall(r'<meta name="description" content="([^"]*)">', text)
        R.check("head", "%s: exactly one meta description, 80-200 characters" % f,
                len(descs) == 1 and text.count('name="description"') == 1 and 80 <= len(htmllib.unescape(descs[0])) <= 200,
                "%d found" % text.count('name="description"'))
        R.check("head", "%s: one viewport meta" % f, text.count('name="viewport"') == 1)
        canon = re.findall(r'<link rel="canonical" href="([^"]*)">', text)
        R.check("head", "%s: canonical link is %s%s" % (f, SITE_BASE, cfg["slug"]), canon == [SITE_BASE + cfg["slug"]], canon)
        for prop, expect in (("og:title", "Kept vs %s | Kept" % cfg["name"]), ("og:description", None),
                             ("og:image", "/icons/icon-512.png"), ("og:type", "website")):
            vals = re.findall(r'<meta property="%s" content="([^"]*)">' % re.escape(prop), text)
            ok = len(vals) == 1 and (htmllib.unescape(vals[0]) == expect if expect else 40 <= len(vals[0]) <= 220)
            R.check("head", "%s: one %s%s" % (f, prop, " = %r" % expect if expect else ""), ok, vals)
        for rel in ('<link rel="icon" href="/icons/favicon-kept.png" sizes="192x192" type="image/png">',
                    '<link rel="apple-touch-icon" href="/icons/apple-touch-icon.png">'):
            R.check("head", "%s: has %s" % (f, rel[:40]), text.count(rel) == 1)
        top, sib_top = text.split("<title>")[0], sib.split("<title>")[0]
        R.check("head", "%s: everything before <title> (doctype, Meta Pixel block, attribution tag, charset, viewport) is identical to %s" % (f, SIBLING),
                top == sib_top)


@check("jsonld")
def check_jsonld(ctx, R):
    R.section("jsonld", "FAQ structured data matches the visible FAQ")
    for f in PAGES:
        text = ctx.text(f)
        blobs = re.findall(r'<script type="application/ld\+json">\s*(.*?)\s*</script>', text, re.S)
        R.check("jsonld", "%s: exactly one JSON-LD block" % f, len(blobs) == 1)
        try:
            data = json.loads(blobs[0])
            faq = [x for x in data["@graph"] if x.get("@type") == "FAQPage"][0]
            qa = [(norm(q["name"]), norm(q["acceptedAnswer"]["text"])) for q in faq["mainEntity"]]
        except Exception as e:   # noqa: BLE001
            R.check("jsonld", "%s: JSON-LD parses as @graph > FAQPage" % f, False, str(e))
            continue
        dom = ctx.dom(f)
        vis = []
        for d in find_all(dom, "details"):
            s = find_all(d, "summary")
            p = find_all(d, "p")
            vis.append((node_text(s[0]) if s else "", node_text(p[0]) if p else ""))
        R.check("jsonld", "%s: FAQPage has at least 2 questions" % f, len(qa) >= 2, len(qa))
        R.check("jsonld", "%s: JSON-LD questions and answers are word for word the visible ones" % f, qa == vis,
                "JSON-LD %r / visible %r" % ([q for q, _ in qa], [q for q, _ in vis]))


@check("pixel")
def check_pixel(ctx, R):
    R.section("pixel", "Meta Pixel block and attribution script")
    tag = '<script src="/attribution.js" defer></script>'
    for f in PAGES:
        text = ctx.text(f)
        R.check("pixel", "%s: pixel init, PageView and the noscript image carry the site's pixel id" % f,
                "fbq('init', '841447128961693');" in text and "fbq('track', 'PageView');" in text
                and "https://www.facebook.com/tr?id=841447128961693&ev=PageView&noscript=1" in text)
        R.check("pixel", "%s: attribution.js right after the 'End Meta Pixel Code' comment, exactly once" % f,
                text.count(tag) == 1 and re.search(r"<!-- End Meta Pixel Code -->\s*" + re.escape(tag), text) is not None
                and text.count("attribution.js") == 1)
        R.check("pixel", "%s: pixel block comes before the attribution tag, which comes before the charset" % f,
                0 <= text.find("<!-- Meta Pixel Code -->") < text.find(tag) < text.find("<meta charset"))
        R.check("pixel", "%s: no Google tag or ad id" % f,
                not re.search(r"googletagmanager|gtag\(|google-analytics|googleadservices|\bAW-\d", text))


@check("links")
def check_links(ctx, R):
    R.section("links", "links")
    for f, cfg in PAGES.items():
        dom = ctx.dom(f)
        hrefs = [a.attrs.get("href", "") for a in find_all(dom, "a")]
        app = [h for h in hrefs if h.startswith("https://app.keptsoftware.com.au")]
        bad = [h for h in app if h not in cfg["app"]]
        R.check("links", "%s: every app link is in an existing form (%s)" % (f, " or ".join(sorted(x.replace("https://app.keptsoftware.com.au", "") or "/" for x in cfg["app"]))), not bad and app, bad)
        start = [h for h in app if h != APP_DEMO]
        R.check("links", "%s: 3 'Get started' links (header, hero, final) and 2 demo links, as on the siblings" % f,
                len(start) == 3 and len(set(start)) == 1 and app.count(APP_DEMO) == 2, "%d start, %d demo" % (len(start), app.count(APP_DEMO)))
        other = [h for h in hrefs if h not in app and h not in OTHER_HREFS]
        R.check("links", "%s: no other links (no competitor links, nothing external)" % f, not other, other)
        tagged = [h for h in hrefs if re.search(r"utm_|[?&]kl=|[?&]kr=|fbclid|gclid", h)]
        R.check("links", "%s: no campaign tags written by hand (attribution.js adds them)" % f, not tagged, tagged)


@check("copy")
def check_copy(ctx, R):
    R.section("copy", "words and claims")
    for f, cfg in PAGES.items():
        copy = ctx.copy_text(f)
        for label, rx in HELD:
            m = rx.search(copy)
            R.check("copy", "%s: no %r" % (f, label), not m, "…%s…" % copy[max(0, m.start() - 40):m.end() + 40] if m else "")
        for label, rx in TONE:
            m = rx.search(copy)
            R.check("copy", "%s: no %s wording" % (f, label), not m, "…%s…" % copy[max(0, m.start() - 40):m.end() + 40] if m else "")
        dom = ctx.dom(f)
        # route optimisation is a Team-plan feature: never offer it for Kept without saying so
        bad = []
        for td in find_all(dom, "td", data_label="Kept"):
            t = node_text(td)
            if re.search(r"route optimi", t, re.I) and "Team plan and above" not in t:
                bad.append(t)
        for s in sentences(visible_text(dom)):
            if re.search(r"\bKept\b", s) and re.search(r"route optimi", s, re.I) and "Team plan" not in s:
                bad.append(s)
        R.check("copy", "%s: route optimisation is only ever claimed for Kept as 'Team plan and above'" % f, not bad, bad)
        h1 = find_all(dom, "h1")
        R.check("copy", "%s: one h1 that names both products" % f,
                len(h1) == 1 and "Kept" in node_text(h1[0]) and cfg["name"] in node_text(h1[0]), [node_text(x) for x in h1])


@check("figures")
def check_figures(ctx, R):
    R.section("figures", "every number is vetted")
    src = ctx.sources()
    for f, cfg in PAGES.items():
        entries = [s for s in src["sources"] if s.get("page") == f]
        dom = ctx.dom(f)
        copy = ctx.copy_text(f)
        page_nums = set(figure_tokens(copy))
        src_nums = set()
        for s in entries:
            for fig in s.get("figures", []):
                src_nums.update(numbers(fig))
        stray = sorted(page_nums - src_nums)
        R.check("figures", "%s: every number on the page is a Kept figure the siblings state or a figure in the source table" % f, not stray, "not in the source table: %s" % stray)
        orphan = sorted(src_nums - page_nums)
        R.check("figures", "%s: every figure in the source table is on the page (no stale entries)" % f, not orphan, "not on the page: %s" % orphan)
        # Kept's dollar figures: only $35 and $229
        dollars = set(re.sub(r"\s", "", d) for d in re.findall(r"\$\s?\d[\d,]*(?:\.\d+)?", copy))
        src_dollars = set(re.sub(r"\s", "", d) for s in entries for fig in s.get("figures", []) for d in re.findall(r"\$\s?\d[\d,]*(?:\.\d+)?", fig))
        extra = sorted(dollars - src_dollars - KEPT_DOLLARS)
        R.check("figures", "%s: Kept's only prices are $35 and $229+ (what the existing pages say); no other dollar amount" % f, not extra, extra)
        # table: Kept cells carry no number but the vetted Kept ones; competitor cells only sourced ones
        rows = [r for r in find_all(dom, "tr")][1:]
        badk, badc = [], []
        for r in rows:
            tds = find_all(r, "td")
            if len(tds) != 3:
                continue
            k, c = node_text(tds[1]), node_text(tds[2])
            if figure_tokens(k):
                badk.append((k, figure_tokens(k)))
            left = [t for t in numbers(DATE_RE.sub(" ", c)) if t not in src_nums]
            if left or any(p.search(c) for p in (KEPT_FIGURES[0], KEPT_FIGURES[1])):
                badc.append((c, left))
        R.check("figures", "%s: Kept's table cells hold only the vetted Kept figures" % f, not badk, badk)
        R.check("figures", "%s: %s's table cells hold only figures from the source table (never a Kept price)" % (f, cfg["name"]), not badc, badc)


@check("sources")
def check_sources(ctx, R):
    R.section("sources", "tools/vs-sources.json")
    try:
        src = ctx.sources()
    except Exception as e:   # noqa: BLE001
        R.check("sources", "vs-sources.json loads", False, str(e))
        return
    entries = src.get("sources", [])
    today = date.today()
    ids = [s.get("id") for s in entries]
    R.check("sources", "ids are unique and every entry names one of the pages", len(ids) == len(set(ids)) and all(s.get("page") in PAGES for s in entries) and entries)
    try:
        checked = datetime.strptime(src.get("checked", ""), "%Y-%m-%d").date()
    except ValueError:
        checked = None
    R.check("sources", "'checked' is a date, not in the future", checked is not None and checked <= today, src.get("checked"))
    bad = []
    for s in entries:
        miss = [k for k in ("id", "page", "claim", "url", "seen", "quote") if not s.get(k)]
        if miss:
            bad.append((s.get("id"), "missing " + ",".join(miss)))
    R.check("sources", "every entry has id, page, claim, url, seen and quote", not bad, bad)
    badurl, baddate, stale = [], [], []
    for s in entries:
        u = urlsplit(s.get("url", ""))
        cfg = PAGES.get(s.get("page"), {})
        if u.scheme != "https" or u.netloc not in cfg.get("hosts", set()):
            badurl.append((s.get("id"), s.get("url")))
        try:
            d = datetime.strptime(s.get("seen", ""), "%Y-%m-%d").date()
            if d > today:
                baddate.append((s.get("id"), s.get("seen")))
            elif (today - d).days > STALE_DAYS:
                stale.append(s.get("id"))
        except ValueError:
            baddate.append((s.get("id"), s.get("seen")))
    R.check("sources", "every URL is https on the competitor's own site or a review site this page names", not badurl, badurl)
    R.check("sources", "every 'seen' date is a real date, not in the future", not baddate, baddate)
    if stale:
        R.warn("sources", "%d source entries were read more than %d days ago (%s...): re-check the prices before relying on the pages" % (len(stale), STALE_DAYS, ", ".join(stale[:3])))
    badfig = []
    for s in entries:
        qn = set(numbers(s.get("quote", "")))
        for fig in s.get("figures", []):
            for n in numbers(fig):
                if n not in qn:
                    badfig.append((s.get("id"), fig, "not in the quoted wording"))
    R.check("sources", "every figure appears in the exact wording quoted for it", not badfig, badfig)
    for f, cfg in PAGES.items():
        text = visible_text(ctx.dom(f))
        mine = [s for s in entries if s.get("page") == f]
        missing = [(s["id"], fr) for s in mine for fr in s.get("page_text", []) if fr not in text]
        R.check("sources", "%s: every page_text fragment in the source table is on the page" % f, not missing, missing)
        R.check("sources", "%s: at least %d sourced entries" % (f, 12), len(mine) >= 12, len(mine))
        named = [site for site in cfg["review_sites"] if site in text]
        nosrc = [site for site in named if not any(cfg["review_sites"][site] in s.get("url", "") for s in mine)]
        R.check("sources", "%s: every review site the page names has a source entry" % f, not nosrc and named, nosrc or "no review site named")
        others = [w for w in ("G2", "Trustpilot", "Capterra", "Xero App Store", "Software Advice", "GetApp", "ProductReview") if w in text and w not in cfg["review_sites"]]
        R.check("sources", "%s: no review site named that is not in the source table" % f, not others, others)
        kept_ok = all(c.get("text") and c.get("from") for c in src.get("kept_claims", []))
        R.check("sources", "kept_claims each say where they come from", kept_ok and src.get("kept_claims"))


@check("table")
def check_table(ctx, R):
    R.section("table", "comparison table")
    src = ctx.sources()
    kept_frags = [c["text"] for c in src.get("kept_claims", [])]
    for f, cfg in PAGES.items():
        dom = ctx.dom(f)
        tables = find_all(dom, "table")
        R.check("table", "%s: one table inside .tablewrap, role=table" % f,
                len(tables) == 1 and tables[0].attrs.get("role") == "table" and tables[0].parent.classes() == ["tablewrap"])
        if len(tables) != 1:
            continue
        rows = find_all(tables[0], "tr")
        head = [node_text(h) for h in find_all(rows[0], "th")]
        R.check("table", "%s: header row is blank | Kept | %s" % (f, cfg["name"]), head == ["", "Kept", cfg["name"]], head)
        R.check("table", "%s: 5 to 9 data rows" % f, 5 <= len(rows) - 1 <= 9, len(rows) - 1)
        label_problems, role_problems, cell_k, cell_c = [], [], [], []
        frags = [fr for s in src["sources"] if s.get("page") == f for fr in s.get("page_text", [])]
        for r in rows[1:]:
            tds = find_all(r, "td")
            if len(tds) != 3:
                label_problems.append("row has %d cells" % len(tds))
                continue
            labels = [t.attrs.get("data-label") for t in tds]
            if labels != ["", "Kept", cfg["name"]]:
                label_problems.append(labels)
            if r.attrs.get("role") != "row" or any(t.attrs.get("role") != "cell" for t in tds):
                role_problems.append(node_text(tds[0]))
            left = uncovered(node_text(tds[1]), kept_frags)
            if left:
                cell_k.append((node_text(tds[1]), left))
            left = uncovered(node_text(tds[2]), frags)
            if left:
                cell_c.append((node_text(tds[2]), left))
        R.check("table", "%s: every cell has the data-label the phone cards show (blank, Kept, %s)" % (f, cfg["name"]), not label_problems, label_problems)
        R.check("table", "%s: rows and cells carry role=row / role=cell like the siblings" % f, not role_problems, role_problems)
        R.check("table", "%s: only the first data row is highlighted (class us)" % f,
                [r.attrs.get("class") for r in rows[1:]] == ["us"] + [None] * (len(rows) - 2), [r.attrs.get("class") for r in rows[1:]])
        R.check("table", "%s: every Kept cell is made of vetted Kept claims (siblings, homepage, APP-CLAIMS)" % f, not cell_k, cell_k)
        R.check("table", "%s: every %s cell is made of sourced fragments from the source table" % (f, cfg["name"]), not cell_c, cell_c)
        notes = [node_text(n) for n in find_all(dom, "p", cls="note")]
        month = None
        try:
            month = datetime.strptime(src["checked"], "%Y-%m-%d").strftime("%B %Y")
        except Exception:   # noqa: BLE001
            pass
        pat = r"^Competitor pricing researched (%s) 20\d\d, from %s's public pricing page — figures change, worth re-checking before quoting anyone directly\." % (MONTHS, re.escape(cfg["name"]))
        m = re.match(pat, notes[0]) if notes else None
        R.check("table", "%s: pricing note reads like the siblings ('researched <month year> … figures change, worth re-checking')" % f, m is not None, notes[:1])
        R.check("table", "%s: the note's month is the month the sources were read (%s)" % (f, month), m is not None and month is not None and ("researched " + month) in notes[0])


@check("structure")
def check_structure(ctx, R):
    R.section("structure", "same skeleton as the sibling pages")
    sib = ctx.text(SIBLING)
    sib_dom = parse(sib)

    def block(t, a, b):
        i, j = t.find(a), t.find(b)
        return t[i:j + len(b)] if 0 <= i < j else None

    def sections(dom):
        body = find_all(dom, "body")[0]
        return [(s.attrs.get("id"), tuple(s.classes())) for s in body.kids if not isinstance(s, str) and s.tag == "section"]

    for f in PAGES:
        t = ctx.text(f)
        dom = parse(t)
        R.check("structure", "%s: font preload and the whole <style> block are identical to %s" % (f, SIBLING),
                block(t, '<link rel="preload"', "</style>") == block(sib, '<link rel="preload"', "</style>") and block(t, '<link rel="preload"', "</style>"))
        norm_app = lambda s: re.sub(r'href="https://app\.keptsoftware\.com\.au/[^"]*"', 'href="APP"', s)
        R.check("structure", "%s: header is the sibling's header (apart from the app link)" % f,
                norm_app(block(t, "<header>", "</header>") or "x") == norm_app(block(sib, "<header>", "</header>")))
        R.check("structure", "%s: footer is identical to %s" % (f, SIBLING), block(t, "<footer>", "</footer>") == block(sib, "<footer>", "</footer>"))
        R.check("structure", "%s: sections are in the siblings' order (hero, table, reviews, FAQ, call to action)" % f, sections(dom) == sections(sib_dom), sections(dom))
        cta = find_all(dom, "div", cls="cta-final")
        scta = find_all(sib_dom, "div", cls="cta-final")
        R.check("structure", "%s: final call to action says what the siblings' says" % f,
                len(cta) == 1 and [node_text(x) for x in find_all(cta[0], "h2") + find_all(cta[0], "p")] == [node_text(x) for x in find_all(scta[0], "h2") + find_all(scta[0], "p")])
        grid = find_all(dom, "div", cls="why-grid")
        R.check("structure", "%s: reviews section has exactly two cards, each an h3 and a paragraph" % f,
                len(grid) == 1 and len(find_all(grid[0], "div", cls="why")) == 2
                and all(len(find_all(w, "h3")) == 1 and len(find_all(w, "p")) == 1 for w in find_all(grid[0], "div", cls="why")))
        R.check("structure", "%s: FAQ section has an id of faq and 2 to 5 questions" % f,
                len(find_all(dom, "section", id="faq")) == 1 and 2 <= len(find_all(dom, "details")) <= 5)
        hero = find_all(dom, "section", cls="hero")
        R.check("structure", "%s: hero has an eyebrow, one h1, a lede and two buttons" % f,
                len(hero) == 1 and len(find_all(hero[0], "span", cls="eyebrow")) == 1 and len(find_all(hero[0], "h1")) == 1
                and len(find_all(hero[0], "p", cls="lede")) == 1 and len(find_all(hero[0], "a")) == 2)


# ---------------------------------------------------------------------------------------------
# Browser checks
# ---------------------------------------------------------------------------------------------
@check("hscroll", browser=True)
def check_hscroll(ctx, R):
    R.section("hscroll", "no horizontal scroll")
    for f in PAGES:
        for w in (375, 1280):
            bctx, page = ctx.open(f, w)
            try:
                m = page.evaluate("""function(){var d=document.documentElement,b=document.body;
                  var off=[].slice.call(document.querySelectorAll('body *')).filter(function(e){var r=e.getBoundingClientRect();return r.right>window.innerWidth+0.5&&r.width>0}).slice(0,4).map(function(e){return e.tagName+'.'+e.className+' right='+Math.round(e.getBoundingClientRect().right)});
                  return {sw:d.scrollWidth,cw:d.clientWidth,bw:b.scrollWidth,iw:window.innerWidth,off:off}}""")
            finally:
                bctx.close()
            R.check("hscroll", "%s at %d px: page is no wider than the screen" % (f, w), m["sw"] <= m["cw"] and m["bw"] <= m["iw"], m)


@check("cards", browser=True)
def check_cards(ctx, R):
    R.section("cards", "table turns into cards on a phone")
    probe = """function(){
      var t=document.querySelector('.tablewrap table'), rows=[].slice.call(t.querySelectorAll('tr')), cs=getComputedStyle;
      var data=rows.slice(1), tds=[].concat.apply([],data.map(function(r){return [].slice.call(r.children).slice(1)}));
      var head=cs(rows[0]);
      return {table:cs(t).display, rows:data.map(function(r){return cs(r).display}), cells:tds.map(function(td){return {d:cs(td).display,c:cs(td,'::before').content,l:td.getAttribute('data-label')}}),
              headHidden: head.position==='absolute' && parseFloat(head.width)<=2, cardW:Math.round(data[0].getBoundingClientRect().width), vw:window.innerWidth}}"""
    for f in PAGES:
        bctx, page = ctx.open(f, 375)
        try:
            m = page.evaluate(probe)
        finally:
            bctx.close()
        R.check("cards", "%s at 375 px: table is a block of cards, header row visually hidden" % f,
                m["table"] == "block" and all(d == "block" for d in m["rows"]) and m["headHidden"], m)
        wrong = [c for c in m["cells"] if c["d"] != "block" or c["c"] != '"%s"' % c["l"]]
        R.check("cards", "%s at 375 px: each cell shows its data-label as a small heading above the text" % f, not wrong and m["cells"], wrong[:3])
        R.check("cards", "%s at 375 px: cards fit inside the screen" % f, m["cardW"] <= m["vw"] - 20, m)
        bctx, page = ctx.open(f, 1280)
        try:
            m = page.evaluate(probe)
        finally:
            bctx.close()
        R.check("cards", "%s at 1280 px: still a real table, no card labels" % f,
                m["table"] == "table" and all(c["c"] in ("none", "normal") for c in m["cells"]), m["table"])


COLLECT_JS = """function(){
  var toRGBA=function(css){var c=document.createElement('canvas');c.width=c.height=1;var x=c.getContext('2d',{willReadFrequently:true});
    x.clearRect(0,0,1,1);x.fillStyle='#000';x.fillStyle=css;x.fillRect(0,0,1,1);var d=x.getImageData(0,0,1,1).data;return [d[0],d[1],d[2],d[3]/255]};
  var out=[],w=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT),n;
  while((n=w.nextNode())){
    var t=n.nodeValue.replace(/\\s+/g,' ').trim(); if(!t) continue;
    var p=n.parentElement; if(!p) continue;
    if(['SCRIPT','STYLE','NOSCRIPT','TEMPLATE'].indexOf(p.tagName)>=0) continue;
    var cs=getComputedStyle(p); if(cs.visibility==='hidden'||cs.display==='none') continue;
    var hidden=false;
    for(var e=p,i=0;e&&i<6;e=e.parentElement,i++){var r0=e.getBoundingClientRect(),s=getComputedStyle(e);
      if((r0.width<=2||r0.height<=2)&&(s.overflow!=='visible'||s.clip!=='auto')){hidden=true;break}}
    if(hidden) continue;
    var op=1; for(var q=p;q;q=q.parentElement) op*=parseFloat(getComputedStyle(q).opacity);
    var range=document.createRange(); range.selectNodeContents(n);
    var rs=range.getClientRects();
    for(var k=0;k<rs.length;k++){var r=rs[k]; if(r.width<3||r.height<3) continue;
      out.push({t:t.slice(0,50),rgba:toRGBA(cs.color),op:op,x:r.left+window.scrollX,y:r.top+window.scrollY,w:r.width,h:r.height})}
  }
  return out}"""

SAMPLE_JS = """async function(a){
  var img=new Image(); img.src='data:image/png;base64,'+a.png; await img.decode();
  var c=document.createElement('canvas'); c.width=img.width; c.height=img.height;
  var ctx=c.getContext('2d',{willReadFrequently:true}); ctx.drawImage(img,0,0);
  var lin=function(v){v/=255;return v<=0.03928?v/12.92:Math.pow((v+0.055)/1.055,2.4)};
  var lum=function(r,g,b){return 0.2126*lin(r)+0.7152*lin(g)+0.0722*lin(b)};
  var bad=[],worst=99;
  a.nodes.forEach(function(nd){
    var al=nd.rgba[3]*nd.op, min=99, at=null, cols=8, rows=Math.max(1,Math.min(3,Math.floor(nd.h/8)));
    for(var i=0;i<cols;i++)for(var j=0;j<rows;j++){
      var sx=Math.floor(nd.x+(i+0.5)/cols*nd.w), sy=Math.floor(nd.y+(j+0.5)/rows*nd.h);
      if(sx<0||sy<0||sx>=c.width||sy>=c.height) continue;
      var p=ctx.getImageData(sx,sy,1,1).data, br=p[0],bg=p[1],bb=p[2];
      var fr=nd.rgba[0]*al+br*(1-al), fg=nd.rgba[1]*al+bg*(1-al), fb=nd.rgba[2]*al+bb*(1-al);
      var L1=lum(fr,fg,fb), L2=lum(br,bg,bb), ratio=(Math.max(L1,L2)+0.05)/(Math.min(L1,L2)+0.05);
      if(ratio<min){min=ratio;at=[br,bg,bb,Math.round(fr),Math.round(fg),Math.round(fb)]}
    }
    if(min<worst) worst=min;
    if(min<a.min) bad.push({t:nd.t,ratio:Math.round(min*100)/100,bgfg:at});
  });
  return {n:a.nodes.length,worst:Math.round(worst*100)/100,nbad:bad.length,bad:bad.slice(0,8)}}"""


def measure_contrast(ctx, f, width, scheme, minimum=4.5):
    bctx, page = ctx.open(f, width, scheme)
    try:
        nodes = page.evaluate(COLLECT_JS)
        page.add_style_tag(content="*,*::before,*::after{color:transparent!important;-webkit-text-fill-color:transparent!important;text-shadow:none!important}")
        png = page.screenshot(full_page=True)
    finally:
        bctx.close()
    blank = ctx.browser.new_page()
    try:
        return blank.evaluate(SAMPLE_JS, {"png": base64.b64encode(png).decode("ascii"), "nodes": nodes, "min": minimum})
    finally:
        blank.close()


@check("contrast", browser=True)
def check_contrast(ctx, R):
    R.section("contrast", "readable text, dark and light")
    for f in PAGES:
        for scheme in ("dark", "light"):
            for w in (375, 1280):
                m = measure_contrast(ctx, f, w, scheme)
                R.check("contrast", "%s, %s mode, %d px: all %d pieces of text have contrast >= 4.5 (lowest %.2f)" % (f, scheme, w, m["n"], m["worst"]),
                        m["nbad"] == 0 and m["n"] > 40, m["bad"] if m["nbad"] else "only %d text pieces found" % m["n"])


@check("errors", browser=True)
def check_errors(ctx, R):
    R.section("errors", "pages load cleanly")
    for f in PAGES:
        bctx, page = ctx.open(f, 1280)
        try:
            page.wait_for_timeout(300)
            errs, bad = list(page.errors), list(page.bad)
            imgs = page.evaluate("[].slice.call(document.images).filter(function(i){return !i.complete||i.naturalWidth===0}).map(function(i){return i.getAttribute('src')})")
        finally:
            bctx.close()
        R.check("errors", "%s: no uncaught page errors" % f, not errs, errs)
        R.check("errors", "%s: every file the page asks the site for is served (no 404s)" % f, not bad, bad)
        R.check("errors", "%s: every image on the page loads" % f, not imgs, imgs)


# ---------------------------------------------------------------------------------------------
# Running, and proving the suite can fail
# ---------------------------------------------------------------------------------------------
def run_checks(ctx, only=None, static=False, echo=True):
    R = Results(echo)
    for group, fn, needs_browser in CHECKS:
        if only and group not in only:
            continue
        if static and needs_browser:
            continue
        try:
            fn(ctx, R)
        except SystemExit:
            raise
        except Exception as e:   # noqa: BLE001  a crash is a failure, not a reason to stop
            R.check(group, "check crashed: %s" % fn.__name__, False, "%s: %s | %s" % (type(e).__name__, e, traceback.format_exc().splitlines()[-3:]))
    return R


def sub1(old, new, count=1):
    """A mutation that must change exactly what it says."""
    def fn(text):
        if old not in text:
            raise AssertionError("mutation target not found: %r" % old[:70])
        return text.replace(old, new, count)
    return fn


def mutations():
    SS, FG = "vs-sortscape.html", "vs-fergus.html"
    J = SOURCES_REL
    add_before_body_end = lambda s: sub1("</body>", s + "\n</body>")
    return [
        # (what is broken, file, mutation, check groups that must catch it)
        ("charset pushed past the first 1024 bytes", SS, sub1('<meta charset="UTF-8">', "<!-- " + "x" * 1100 + " -->\n<meta charset=\"UTF-8\">"), ["head"]),
        ("a second <title>", FG, sub1("</title>", "</title>\n<title>Second</title>"), ["head"]),
        ("meta description removed", SS, sub1('<meta name="description"', '<meta name="x-description"'), ["head"]),
        ("canonical points at another page", FG, sub1('href="https://www.keptsoftware.com.au/vs-fergus"', 'href="https://www.keptsoftware.com.au/vs-jobber"'), ["head"]),
        ("og:image removed", SS, sub1('<meta property="og:image"', '<meta property="og:imagex"'), ["head"]),
        ("viewport meta removed", FG, sub1('<meta name="viewport"', '<meta name="viewportx"'), ["head"]),
        ("JSON-LD answer no longer matches the visible answer", SS, sub1('"text": "SortScape says it was made exclusively', '"text": "SortScape says it was built exclusively'), ["jsonld"]),
        ("JSON-LD question changed", FG, sub1('"name": "Does Fergus have a free plan?"', '"name": "Does Fergus have a free tier?"'), ["jsonld"]),
        ("pixel init removed", FG, sub1("fbq('init', '841447128961693');", ""), ["pixel", "head"]),
        ("attribution script moved above the pixel comment", SS, lambda t: t.replace('  <script src="/attribution.js" defer></script>\n', "", 1).replace("<!-- Meta Pixel Code -->", '<script src="/attribution.js" defer></script>\n<!-- Meta Pixel Code -->', 1), ["pixel"]),
        ("attribution script written twice", FG, sub1('<script src="/attribution.js" defer></script>', '<script src="/attribution.js" defer></script>\n  <script src="/attribution.js" defer></script>'), ["pixel"]),
        ("app link with campaign tags written by hand", SS, sub1('href="https://app.keptsoftware.com.au/?industry=lawn_care"', 'href="https://app.keptsoftware.com.au/?industry=lawn_care&utm_source=x"'), ["links"]),
        ("app link in a form the siblings don't use", FG, sub1('href="https://app.keptsoftware.com.au/"', 'href="https://app.keptsoftware.com.au/?industry=roofing"'), ["links"]),
        ("a link out to the competitor", SS, sub1("Capterra and the Xero App Store, read", '<a href="https://sortscape.com.au/">Capterra</a> and the Xero App Store, read'), ["links"]),
        ("'tax invoice' appears", SS, sub1("Is SortScape cheaper than Kept?", "Is SortScape cheaper than Kept for tax invoices?", 2), ["copy"]),
        ("'Pay now' appears", FG, sub1("Does Fergus have a free plan?", "Does Fergus have a Pay now button?", 2), ["copy"]),
        ("'automatically' appears", SS, sub1("Kept's Free plan costs nothing", "Kept's Free plan automatically costs nothing"), ["copy"]),
        ("'AI' appears", FG, sub1("assistant tools", "AI assistant tools"), ["copy"]),
        ("'encryption' appears", SS, sub1("Good to know.", "Good to know about encryption."), ["copy"]),
        ("'free forever' appears", FG, sub1("Start free. No card, no time limit.", "Start free. Free forever.", 1), ["copy", "structure"]),
        ("'testimonial' appears", SS, sub1("Good to know.", "Good to know, with testimonials."), ["copy"]),
        ("a superlative about Kept", SS, sub1("Kept is worth a look if", "Kept is the best choice if"), ["copy"]),
        ("'better than'", FG, sub1("Try each on a few real jobs", "Kept is better than Fergus, so try each on a few real jobs"), ["copy"]),
        ("disparagement", SS, sub1("Lawn and garden maintenance</td>", "Lawn and garden maintenance, clunky</td>"), ["copy", "table"]),
        ("an unsourced negative claim", FG, sub1("Applies GST and syncs", "Lacks proper GST and syncs"), ["copy", "table"]),
        ("route optimisation claimed for Kept without 'Team plan and above'", SS, sub1("; route optimisation on Team plan and above", "; route optimisation"), ["copy", "table"]),
        ("a new Kept price", SS, sub1("Kept is worth a look if", "Kept's Solo plan is $49 a month, so Kept is worth a look if"), ["figures"]),
        ("the founding offer's price", FG, sub1("Try each on a few real jobs", "Kept's first year is $21/mo, so try each on a few real jobs"), ["figures", "copy"]),
        ("a competitor price changed on the page only", SS, sub1("From AUD $15/mo for 1 user", "From AUD $16/mo for 1 user"), ["figures", "table", "sources"]),
        ("a competitor price swapped for a Kept price", FG, sub1("Essentials from $53/mo", "Essentials from $35/mo"), ["figures", "table", "sources"]),
        ("a rating changed on the page only", FG, sub1("4.6 out of 5 on Capterra (155 reviews)", "4.7 out of 5 on Capterra (155 reviews)"), ["figures", "sources"]),
        ("unsourced competitor claim added to a table cell", SS, sub1("<td role=\"cell\" data-label=\"SortScape\">Lawn and garden maintenance</td>", "<td role=\"cell\" data-label=\"SortScape\">Lawn and garden maintenance and landscaping</td>"), ["table"]),
        ("unvetted Kept claim added to a table cell", FG, sub1("Turf/reno soil, bond-clean and house-wash calculators built in;", "Turf/reno soil, bond-clean and house-wash calculators built in, plus offline photo capture;"), ["table"]),
        ("source table: a figure that is not in the wording quoted for it", J, sub1('"figures": ["25", "150"]', '"figures": ["25", "151"]'), ["sources", "figures"]),
        ("source table: URL on an unexpected host", J, sub1('"url": "https://sortscape.com.au/pricing/", "seen": "2026-10-24",\n      "quote": "Premium AUD $29/month', '"url": "https://example.com/pricing/", "seen": "2026-10-24",\n      "quote": "Premium AUD $29/month'), ["sources"]),
        ("source table: date in the future", J, sub1('"id": "FG-03", "page": "vs-fergus.html",\n      "claim": "Essentials is from $53 a month, Professional from $77 a month, and a custom plan is offered for more than 10 staff",\n      "url": "https://fergus.com/au/pricing/", "seen": "2026-10-24"', '"id": "FG-03", "page": "vs-fergus.html",\n      "claim": "Essentials is from $53 a month, Professional from $77 a month, and a custom plan is offered for more than 10 staff",\n      "url": "https://fergus.com/au/pricing/", "seen": "2031-01-01"'), ["sources"]),
        ("source table: a stale figure the page no longer shows", J, sub1('"quote": "Premium AUD $29/month Get your business to the next level",\n      "figures": ["$29"]', '"quote": "Premium AUD $29/month $99 Get your business to the next level",\n      "figures": ["$29", "$99"]'), ["figures"]),
        ("source table: a page_text fragment the page no longer says", J, sub1('"page_text": ["a requests inbox"]', '"page_text": ["a requests inbox", "something the page never said"]'), ["sources"]),
        ("a review site named with no source", SS, sub1("Capterra and the Xero App Store, read", "Capterra, G2 and the Xero App Store, read"), ["sources"]),
        ("table cell loses its data-label", FG, sub1('data-label="Fergus">Per user, month to month', 'data-label="">Per user, month to month'), ["table", "cards"]),
        ("pricing note loses 'figures change'", SS, sub1("figures change, worth re-checking before quoting anyone directly", "figures are correct"), ["table"]),
        ("pricing note names an older month", FG, sub1("Competitor pricing researched October 2026", "Competitor pricing researched July 2026"), ["table"]),
        ("FAQ section loses its id", SS, lambda t: t.replace('<section id="faq">', '<section id="faq-moved">'), ["structure"]),
        ("CSS changed", FG, sub1(".note{font-size:.8rem;", ".note{font-size:.7rem;"), ["structure"]),
        ("footer edited", SS, sub1("Privacy Policy</a>", "Privacy</a>"), ["structure"]),
        ("a third review card", FG, sub1('<div class="why-grid">', '<div class="why-grid">\n      <div class="why"><h3>x</h3><p>y</p></div>'), ["structure"]),
        ("something 600 px wide: horizontal scroll on a phone", SS, add_before_body_end('<div style="width:600px;height:10px;background:#000"></div>'), ["hscroll"]),
        ("something 1400 px wide: horizontal scroll on desktop", FG, add_before_body_end('<div style="width:1400px;height:10px;background:#000"></div>'), ["hscroll"]),
        ("phone cards broken: cells no longer stack", SS, sub1(".tablewrap td{display:block;", ".tablewrap td{display:table-cell;"), ["cards", "structure"]),
        ("dark mode: body text too dim", FG, sub1("</style>", "@media (prefers-color-scheme: dark){.why p{color:#3d4d43!important}}\n</style>"), ["contrast", "structure"]),
        ("light mode: notes too pale", SS, sub1("</style>", ".note{color:#c9d2cd!important}\n</style>"), ["contrast", "structure"]),
        ("dark mode: text on the hero gradient too dim", FG, sub1("</style>", "@media (prefers-color-scheme: dark){.hero p.lede{color:#1d3a2a!important}}\n</style>"), ["contrast", "structure"]),
        ("an image that 404s", SS, add_before_body_end('<img src="/icons/not-there.svg" alt="">'), ["errors"]),
        ("a script that throws", FG, add_before_body_end("<script>nonexistentFunction()</script>"), ["errors"]),
    ]


def selftest(args):
    tmp = Path(tempfile.mkdtemp(prefix="vs-selftest-"))
    pristine, work = tmp / "pristine", tmp / "work"
    ctx = None
    try:
        (pristine / "tools").mkdir(parents=True)
        for f in list(PAGES) + [SIBLING, "attribution.js"]:
            shutil.copy2(str(SITE / f), str(pristine / f))
        for sub in ("fonts", "icons"):
            shutil.copytree(str(SITE / sub), str(pristine / sub))
        shutil.copy2(str(SITE / SOURCES_REL), str(pristine / SOURCES_REL))
        shutil.copytree(str(pristine), str(work))
        ctx = Ctx(work)
        print("selftest: temp copy in %s" % work)
        print("selftest: baseline (the untouched copy must pass everything)")
        base = run_checks(ctx, static=args.static, echo=False)
        for w in base.warns:
            print("  WARN [%s] %s" % w)
        if base.failed:
            print("selftest FAILED: the untouched copy does not pass:")
            for g, n, _, d in base.failed[:10]:
                print("  FAIL [%s] %s -> %s" % (g, n, d))
            return 1
        print("  baseline ok: %d checks pass" % len(base.rows))
        uncaught, all_groups = [], set()
        muts = mutations()
        covered = set()
        for what, f, fn, groups in muts:
            if args.static and all(g in ("hscroll", "cards", "contrast", "errors") for g in groups):
                continue
            path = work / f
            original = (pristine / f).read_bytes().decode("utf-8")
            try:
                mutated = fn(original)
            except AssertionError as e:
                print("selftest BROKEN: mutation %r cannot be applied (%s)" % (what, e))
                uncaught.append(what)
                continue
            if mutated == original:
                print("selftest BROKEN: mutation %r changed nothing" % what)
                uncaught.append(what)
                continue
            path.write_bytes(mutated.encode("utf-8"))
            try:
                R = run_checks(ctx, only=set(groups), static=args.static, echo=False)
            finally:
                shutil.copy2(str(pristine / f), str(path))
            hit = R.failed_groups() & set(groups)
            covered |= hit
            status = "caught by %s" % ", ".join(sorted(R.failed_groups())) if hit else "NOT CAUGHT (wanted %s)" % "/".join(groups)
            print("  %-4s %s -> %s" % ("ok" if hit else "MISS", what, status))
            if not hit:
                uncaught.append(what)
        wanted = set(g for g, _, b in CHECKS if not (args.static and b))
        never = sorted(wanted - covered)
        if never:
            print("selftest: groups never made to fail: %s" % ", ".join(never))
        final = run_checks(ctx, static=args.static, echo=False)
        if final.failed:
            print("selftest FAILED: the copy does not pass again once restored")
            return 1
        if uncaught or never:
            print("selftest FAILED: %d mutation(s) not caught: %s" % (len(uncaught), "; ".join(uncaught)))
            return 1
        print("selftest PASSED: %d deliberate breakages, every one caught; every check group failed at least once; restored copy passes (%d checks)" % (len(muts) if not args.static else len([m for m in muts if not all(g in ("hscroll", "cards", "contrast", "errors") for g in m[3])]), len(final.rows)))
        return 0
    finally:
        if ctx is not None:
            ctx.close()
        shutil.rmtree(str(tmp), ignore_errors=True)


def main():
    ap = argparse.ArgumentParser(description="Checks for vs-sortscape.html and vs-fergus.html")
    ap.add_argument("--static", action="store_true", help="skip the checks that need a browser")
    ap.add_argument("--only", help="comma-separated check groups (%s)" % ",".join(g for g, _, _ in CHECKS))
    ap.add_argument("--selftest", action="store_true", help="break a temp copy on purpose and check the suite goes red each time")
    args = ap.parse_args()
    if args.selftest:
        sys.exit(selftest(args))
    ctx = Ctx(SITE)
    try:
        R = run_checks(ctx, only=set(args.only.split(",")) if args.only else None, static=args.static)
    finally:
        ctx.close()
    n = len(R.rows)
    print("\n%s: %d passed, %d failed (%d checks%s)" % ("FAIL" if R.failed else "PASS", n - len(R.failed), len(R.failed), n,
                                                       ", %d warning(s)" % len(R.warns) if R.warns else ""))
    sys.exit(1 if R.failed else 0)


if __name__ == "__main__":
    main()
