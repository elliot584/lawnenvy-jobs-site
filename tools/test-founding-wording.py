#!/usr/bin/env python3
"""The founding-member wording on the home page shows only while the live counter says spots are left, and the trade pages no longer mention the founding rate.

    $PY tools/test-founding-wording.py             run the checks (Playwright; the counter is answered by this test, the Meta and Google hosts are blocked)
    $PY tools/test-founding-wording.py --selftest  breaks a temp copy of the pages on purpose, several ways, and shows these checks catch each

Why: the offer is "the first 100 businesses pay $21 a month". When the 100th spot goes, a page that still says so advertises a price people can no longer get, and a static page cannot
know that. So the banner and the "$21" line on the Solo card are in the page but hidden, and show only when https://app.keptsoftware.com.au/api/leads confirms spots are left. When
it says none are left, or cannot be read at all (a failed request, an answer that is not a number, JavaScript off), they stay hidden. This checks every one of those answers, that
nothing shows before the answer arrives (no flash of a price that may be gone), that nothing about the offer is left in the visible text at zero, that the shown banner does not make a
phone scroll sideways, and that the four trade pages' pricing note no longer points at "the founding-member rate".
"""
import functools, http.server, json, os, pathlib, re, shutil, socketserver, sys, tempfile, threading

ROOT = pathlib.Path(os.environ.get("KEPT_FOUNDING_ROOT") or pathlib.Path(__file__).resolve().parent.parent)
COUNTER = "https://app.keptsoftware.com.au/api/leads"
TRADE_PAGES = ["clean/index.html", "handyman/index.html", "lawn-care/index.html", "wash/index.html"]
PAGES = ["index.html"] + TRADE_PAGES
SHOWN = [100, 37, 2, 1]                                                  # spots left: the offer is on
UNREADABLE = [   # every answer that must leave the offer hidden: (what, how the test answers)
    ("zero left", ("json", {"ok": True, "claimed": 100, "remaining": 0})),
    ("a counter that is null", ("json", {"ok": True, "claimed": None, "remaining": None})),
    ("an answer with no remaining at all", ("json", {"ok": True})),
    ("ok false", ("json", {"ok": False, "remaining": 50})),
    ("a number in a string", ("json", {"ok": True, "remaining": "5"})),
    ("a negative number", ("json", {"ok": True, "remaining": -3})),
    ("an object", ("json", {"ok": True, "remaining": {"n": 5}})),
    ("a list", ("json", [1, 2, 3])),
    ("an answer that is not JSON", ("text", "<html>Bad gateway</html>")),
    ("an empty answer", ("text", "")),
    ("a server error", ("status", 500)),
    ("a missing endpoint", ("status", 404)),
    ("a request that fails", ("abort", None)),
]


class Quiet(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args, **kwargs):
        pass


def serve(root):
    handler = functools.partial(Quiet, directory=str(root))
    httpd = socketserver.TCPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    return httpd, "http://127.0.0.1:%d/" % httpd.server_address[1]


def answerer(how, held=None):
    """A route handler for the counter. how = ('json', obj) | ('text', s) | ('status', n) | ('abort', None) | ('hold', obj): the last keeps the request waiting (held.append(route)) until the test answers it."""
    def handle(route):
        kind, arg = how
        cors = {"Access-Control-Allow-Origin": "*"}
        if kind == "json":
            route.fulfill(status=200, content_type="application/json", headers=cors, body=json.dumps(arg))
        elif kind == "text":
            route.fulfill(status=200, content_type="application/json", headers=cors, body=arg)
        elif kind == "status":
            route.fulfill(status=arg, content_type="application/json", headers=cors, body=json.dumps({"message": "no"}))
        elif kind == "abort":
            route.abort()
        elif kind == "hold":
            held.append(route)
    return handle


def open_page(browser, base, rel, width, how, held=None, scheme="light"):
    ctx = browser.new_context(viewport={"width": width, "height": 900}, color_scheme=scheme)
    page = ctx.new_page()
    page.route("**/*", lambda r: r.abort() if any(x in r.request.url for x in ("facebook", "google", "googletagmanager")) else r.continue_())
    page.route(COUNTER, answerer(how, held))
    page.goto(base + rel, wait_until="load")
    return ctx, page


def settle(page):
    page.wait_for_timeout(350)   # the counter's answer is stubbed and local: a third of a second is far more than it needs


def state(page):
    return page.evaluate("""() => ({
        banner: !!document.getElementById('founderBanner') && !document.getElementById('founderBanner').hidden && getComputedStyle(document.getElementById('founderBanner')).display !== 'none',
        sub: !!document.getElementById('founderPriceSub') && !document.getElementById('founderPriceSub').hidden && getComputedStyle(document.getElementById('founderPriceSub')).display !== 'none',
        tile: (() => { const t = document.getElementById('founderSlotsTile'); return !!t && getComputedStyle(t).display !== 'none' && t.getBoundingClientRect().width > 0; })(),
        count: (document.getElementById('founderSlotsCount') || {}).textContent,
        text: document.body.innerText,
        over: document.documentElement.scrollWidth - document.documentElement.clientWidth
    })""")


def run(root, quick=False):
    """quick: fewer widths, colour schemes and answers, for the many runs of --selftest (every kind of answer still has its turn at one width)."""
    from playwright.sync_api import sync_playwright
    httpd, base = serve(root)
    problems, checked = [], [0]

    def check(ok, what):
        checked[0] += 1
        if not ok:
            problems.append(what)

    # the pages themselves, as served: hidden from the start, so nothing can flash and a page without JavaScript never shows a price that may be gone
    html = (root / "index.html").read_text(encoding="utf-8")
    check(re.search(r'<div class="founder-banner" id="founderBanner" hidden>', html) is not None, "index.html: the founding banner is not hidden in the page as served")
    check(re.search(r'<div class="price-sub" id="founderPriceSub" hidden>', html) is not None, "index.html: the Solo card's $21 line is not hidden in the page as served")
    check(".founder-banner[hidden]{display:none}" in html, "index.html: nothing makes the hidden banner stay hidden (its own display rule would show it)")
    for rel in TRADE_PAGES:
        t = (root / rel).read_text(encoding="utf-8")
        check(not re.search(r"founding", t, re.I), "%s still mentions the founding offer" % rel)
        check('Full pricing detail: <a href="/#pricing"' in t, "%s lost its pointer to the main pricing page" % rel)

    with sync_playwright() as p:
        browser = p.chromium.launch()
        # spots left: the offer shows, on a desktop and on phones, in both colour schemes
        for left in (SHOWN[:1] + SHOWN[-1:] if quick else SHOWN):
            for width in ((1280, 320) if quick else (1280, 375, 320)):
                for scheme in (("light",) if quick else ("light", "dark")):
                    ctx, page = open_page(browser, base, "index.html", width, ("json", {"ok": True, "claimed": 100 - left, "remaining": left}), scheme=scheme)
                    settle(page)
                    s = state(page)
                    where = "%d left at %d px (%s)" % (left, width, scheme)
                    check(s["banner"] and s["sub"] and s["tile"], "%s: the offer is not showing (banner %s, Solo line %s, tile %s)" % (where, s["banner"], s["sub"], s["tile"]))
                    check(s["count"] == str(left), "%s: the tile says %r" % (where, s["count"]))
                    words = s["text"].lower()   # innerText applies the page's upper-casing of the small labels
                    check("$21" in words and "first 100" in words and "spots left" in words, "%s: the wording is not on the page" % where)
                    check(s["over"] <= 1, "%s: the page scrolls sideways by %d px" % (where, s["over"]))
                    ctx.close()
        # no spots left, or no usable answer: nothing about the offer is visible anywhere
        for what, how in UNREADABLE:
            for width in ((375,) if quick else (1280, 375)):
                ctx, page = open_page(browser, base, "index.html", width, how)
                settle(page)
                s = state(page)
                where = "%s at %d px" % (what, width)
                check(not s["banner"] and not s["sub"] and not s["tile"], "%s: the offer is showing (banner %s, Solo line %s, tile %s)" % (where, s["banner"], s["sub"], s["tile"]))
                left_over = [w for w in ("$21", "first 100", "founding-member", "spots left") if w in s["text"].lower()]
                check(not left_over, "%s: the visible page still says %s" % (where, left_over))
                check("$35" in s["text"], "%s: the Solo price itself went missing" % where)
                ctx.close()
        # before the counter answers nothing shows; when it answers with spots left, the offer appears
        held = []
        ctx, page = open_page(browser, base, "index.html", 1280, ("hold", None), held)
        page.wait_for_timeout(300)
        s = state(page)
        check(len(held) == 1, "the page did not ask the counter exactly once (%d requests)" % len(held))
        check(not s["banner"] and not s["sub"] and "$21" not in s["text"], "the offer shows before the counter has answered")
        if held:
            held[0].fulfill(status=200, content_type="application/json", headers={"Access-Control-Allow-Origin": "*"}, body=json.dumps({"ok": True, "claimed": 60, "remaining": 40}))
            page.wait_for_timeout(300)
            s = state(page)
            check(s["banner"] and s["sub"] and s["count"] == "40", "the offer did not appear when the counter answered 40 left")
        ctx.close()
        # and the other way: an answer of zero that arrives late keeps it hidden
        held = []
        ctx, page = open_page(browser, base, "index.html", 1280, ("hold", None), held)
        page.wait_for_timeout(200)
        if held:
            held[0].fulfill(status=200, content_type="application/json", headers={"Access-Control-Allow-Origin": "*"}, body=json.dumps({"ok": True, "claimed": 100, "remaining": 0}))
            page.wait_for_timeout(300)
            s = state(page)
            check(not s["banner"] and not s["sub"] and "$21" not in s["text"], "the offer shows after the counter answered zero")
        ctx.close()
        # the trade pages hold no founding wording in what a visitor sees
        for rel in TRADE_PAGES:
            ctx, page = open_page(browser, base, rel, 375, ("json", {"ok": True, "remaining": 40}))
            settle(page)
            check(not re.search(r"founding|first 100|\$21", page.evaluate("document.body.innerText"), re.I), "%s: the visible page mentions the founding offer" % rel)
            ctx.close()
        browser.close()
    httpd.shutdown()
    return problems, checked[0]


# --selftest: each damage is applied to a private copy of the five pages, and the checks are run against it. (what is broken, file, the exact text, what replaces it)
DAMAGES = [
    ("the banner is shown from the start", "index.html", '<div class="founder-banner" id="founderBanner" hidden>', '<div class="founder-banner" id="founderBanner">'),
    ("the Solo card's $21 line is shown from the start", "index.html", '<div class="price-sub" id="founderPriceSub" hidden>', '<div class="price-sub" id="founderPriceSub">'),
    ("the hidden banner is overridden by its own display rule", "index.html", ".founder-banner[hidden]{display:none}\n", "\n"),
    ("zero spots left still shows the offer", "index.html", "|| data.remaining <= 0) return;", "|| data.remaining < 0) return;"),
    ("an answer that is not a number shows the offer", "index.html", "!Number.isFinite(data.remaining) ||", ""),
    ("the banner is never shown, even with spots left", "index.html", "document.getElementById('founderBanner').hidden = false;", ""),
    ("the Solo line is never shown, even with spots left", "index.html", "document.getElementById('founderPriceSub').hidden = false;", ""),
    ("a trade page still points at the founding rate", "wash/index.html", 'Full pricing detail: <a href="/#pricing"', 'Full pricing detail and the founding-member rate: <a href="/#pricing"'),
]


def selftest():
    r = run(ROOT)
    if r[0]:
        print("selftest  the unbroken pages do not pass their own checks:\n  " + "\n  ".join(r[0][:8]))
        return 1
    print("selftest  control   the unbroken pages pass (%d checks)" % r[1])
    bad = 0
    for what, rel, old, new in DAMAGES:
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="founding-wording-selftest-"))
        try:
            for f in PAGES:
                (tmp / f).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(ROOT / f, tmp / f)
            text = (tmp / rel).read_text(encoding="utf-8")
            if text.count(old) != 1:
                print("selftest  MISSED   %s  (the text to break occurs %d times in %s: the page was edited, update DAMAGES)" % (what, text.count(old), rel))
                bad += 1
                continue
            (tmp / rel).write_text(text.replace(old, new), encoding="utf-8")
            problems, _ = run(tmp, quick=True)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        print("selftest  %-8s %s" % ("caught" if problems else "MISSED", what))
        bad += 0 if problems else 1
    print("selftest: %d of %d damages caught" % (len(DAMAGES) - bad, len(DAMAGES)))
    return 1 if bad else 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    problems, checked = run(ROOT)
    for p in problems:
        print("FAIL  " + p)
    if problems:
        print("FAIL: %d of %d checks failed" % (len(problems), checked))
        return 1
    print("PASS: %d checks: the founding wording shows only while the counter says spots are left, nothing shows before it answers, and the trade pages no longer mention the founding rate" % checked)
    return 0


if __name__ == "__main__":
    sys.exit(main())
