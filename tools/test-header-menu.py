#!/usr/bin/env python3
"""The site header on the home page and the four trade pages: the link to the customer request page, and the menu button that holds the links on phones and tablets.

    $PY tools/test-header-menu.py             run the checks (Playwright: WebKit in light, Chromium in dark; Meta and Google hosts are blocked)

Why: on 11 November 2026 the founder pointed out that a phone had no way to the request page (the header links vanished below 840 px with nothing in their place)
and that the link's wording, "Need a quote instead?", could be read as a quote for Kept itself. The fix gave phones a menu button and the link the wording
"Need work done?". Building it turned up two more things that this test now guards: the page's global rule for the FAQ <details> (white card, padding, a "+" after the
summary) leaked into the menu and made the header 109 px tall and the page 8 px too wide at 320 px, and the home page's seven links had been squeezed onto two lines
between 841 and about 1060 px. Each of those makes a check below fail when put back. He then asked for a visible "Need work done?" line under the hero buttons as well, so a phone
sees the way to the request page without opening the menu: first on the home page, then on the four trade pages (12 November 2026); the checks on that line are below.

What it checks, on index.html, lawn-care, clean, wash and handyman (each page's breakpoint is read from its own CSS):
  - the two lists agree: every link in the menu is also in the header links, in the same order, with the same address; the old wording is gone from the page
  - at ten widths from 320 to 1440 px and either side of the breakpoint: no sideways scroll, the header is one line tall, the Get started free button never wraps.
    Below the breakpoint the links are folded away and a 44 px menu button sits at the right margin with room before it; above it the links show on one line,
    with at least 12 px to the logo and to the button, and the menu button is hidden
  - the menu opens with its button; all its links are on screen and at least 40 px tall; it closes after a tap on a link (an in-page link also scrolls the page), after a
    tap outside it, and on Escape (the focus goes back to the button); the quote tile says "Need work done?" and reaches the request page
  - without nav.js the button still opens and closes the menu
  - on every page the "Need work done?" line under the two hero buttons shows exactly where the header links are folded away (and not above that), goes to the same address
    as the menu tile, sits between the last button and the proof list, is at least 24 px tall to tap, reaches the request page when tapped (the trade pages are one
    folder down, so they need the leading slash), and on a 390 px phone ends within the first 700 px, so it is on the first screen
"""
import functools, http.server, os, pathlib, re, socketserver, sys, threading

ROOT = pathlib.Path(os.environ.get("KEPT_HEADER_ROOT") or pathlib.Path(__file__).resolve().parent.parent)
PAGES = ["index.html", "lawn-care/index.html", "clean/index.html", "wash/index.html", "handyman/index.html"]
BASE_WIDTHS = [320, 360, 375, 390, 414, 540, 768, 1024, 1280, 1440]
OLD_LABEL, NEW_LABEL, TILE_SUB = "Need a quote instead?", "Need work done?", "Get free quotes from local businesses"
BLOCKED = ("facebook", "google", "googletagmanager")
IGNORED_CONSOLE = ("ERR_FAILED", "Failed to load resource", "CORS policy", "access control checks", "Access-Control-Allow-Origin")
BP_RE = re.compile(r"@media\(max-width:(\d+)px\)\{\.nav-links\{display:none\}\.navmenu\{display:block\}\}")
HERO_BP_RE = re.compile(r"@media\(max-width:(\d+)px\)\{\.hero-work\{display:block\}\}")

problems, checks = [], [0]


def ok(cond, msg):
    checks[0] += 1
    if not cond:
        problems.append(msg)
        print("FAIL  " + msg)


GEOM = """() => {
  const q = s => document.querySelector(s);
  const box = e => { if (!e) return null; const b = e.getBoundingClientRect(); return {l: b.left, r: b.right, w: b.width, h: b.height}; };
  const shown = e => !!e && getComputedStyle(e).display !== 'none' && e.getBoundingClientRect().width > 0;
  return {vw: document.documentElement.clientWidth, sw: document.documentElement.scrollWidth, brand: box(q('header .brand')), ul: box(q('header .nav-links')),
    linksShown: shown(q('header .nav-links')), cta: box(q('header .btn-sm')), menu: box(q('header details.navmenu > summary')), menuShown: shown(q('header details.navmenu')),
    header: box(q('header')), links: [...document.querySelectorAll('header .nav-links a')].map(a => ({text: a.textContent.trim(), h: a.getBoundingClientRect().height}))};
}"""

LISTS = """() => ({
  header: [...document.querySelectorAll('header .nav-links a')].map(a => [a.getAttribute('href'), a.textContent.trim()]),
  menu: [...document.querySelectorAll('header .navmenu-list li:not(.navmenu-work) a')].map(a => [a.getAttribute('href'), a.textContent.trim()]),
  tile: [...document.querySelectorAll('header .navmenu-work a')].map(a => [a.getAttribute('href'), a.textContent.trim()])
})"""

QUIET_SPOT = """() => { for (let y = 780; y > 300; y -= 12) for (const x of [8, 100, 200, 300, 382]) { const el = document.elementFromPoint(x, y);
  if (el && !el.closest('a,button,summary,details,input,select,textarea,label,[onclick]')) return [x, y]; } return null; }"""


HERO = """() => { const e = document.querySelector('.hero-work'); if (!e) return null; const a = e.querySelector('a');
  const r = x => { const b = x.getBoundingClientRect(); return {t: b.top, b: b.bottom, h: b.height}; }; const btns = [...document.querySelectorAll('.hero .hero-ctas .btn')];
  const tile = document.querySelector('header .navmenu-work a');
  return {shown: getComputedStyle(e).display !== 'none', link: r(a), href: a.getAttribute('href'), tileHref: tile && tile.getAttribute('href'), text: e.textContent.trim(), lastBtn: r(btns[btns.length - 1]),
    proof: r(document.querySelector('.hero-proof')), sw: document.documentElement.scrollWidth, vw: document.documentElement.clientWidth}; }"""


def new_page(browser, w, scheme, h=800):
    ctx = browser.new_context(viewport={"width": w, "height": h}, color_scheme=scheme)
    page = ctx.new_page()
    page.route("**/*", lambda r: r.abort() if any(x in r.request.url for x in BLOCKED) else r.continue_())
    return ctx, page


def geometry(browser, base, engine, scheme, rel, bp):
    widths = sorted(set(BASE_WIDTHS + [bp, bp + 1]))
    for w in widths:
        ctx, page = new_page(browser, w, scheme)
        page.goto(base + rel, wait_until="load")
        page.evaluate("document.fonts.ready.then(() => true)")
        page.wait_for_timeout(100)
        g = page.evaluate(GEOM)
        tag = "%s %s %s at %d px" % (engine, scheme, rel, w)
        ok(g["sw"] <= g["vw"] + 1, "%s: the page is %d px wide in a %d px window" % (tag, g["sw"], g["vw"]))
        ok(g["cta"] and g["cta"]["h"] <= 46, "%s: the Get started free button is %s px tall (it wraps)" % (tag, g["cta"] and round(g["cta"]["h"])))
        ok(g["header"]["h"] <= 90, "%s: the header is %d px tall" % (tag, g["header"]["h"]))
        if w <= bp:
            ok(not g["linksShown"], "%s: the links should be folded away at this width" % tag)
            ok(g["menuShown"] and g["menu"] and abs(g["menu"]["w"] - 44) < 1 and abs(g["menu"]["h"] - 44) < 1, "%s: the menu button is missing or not 44 x 44: %s" % (tag, g["menu"]))
            if g["menu"] and g["menu"]["w"]:
                ok(g["menu"]["r"] <= g["vw"] - 19, "%s: the menu button is %d px from the right edge" % (tag, g["vw"] - g["menu"]["r"]))
                ok(g["cta"]["r"] <= g["menu"]["l"] - 3, "%s: the button and the menu button touch" % tag)
            ok(g["brand"]["r"] <= g["cta"]["l"] - 6, "%s: the logo and the Get started free button are %d px apart" % (tag, g["cta"]["l"] - g["brand"]["r"]))
        else:
            ok(g["linksShown"], "%s: the links should show at this width" % tag)
            ok(not g["menuShown"], "%s: the menu button should be hidden at this width" % tag)
            ok(all(l["h"] <= 28 for l in g["links"]), "%s: a link wraps onto two lines: %s" % (tag, [l["text"] for l in g["links"] if l["h"] > 28]))
            if g["ul"]:
                ok(g["brand"]["r"] + 12 <= g["ul"]["l"], "%s: the logo (right %d) and the links (left %d) are too close" % (tag, g["brand"]["r"], g["ul"]["l"]))
                ok(g["ul"]["r"] + 12 <= g["cta"]["l"], "%s: the links (right %d) and the button (left %d) are too close" % (tag, g["ul"]["r"], g["cta"]["l"]))
        ctx.close()


def hero_link(browser, base, engine, scheme, rel, bp):
    for w in sorted(set([320, 390, 414, 768, 900, 1024, 1280, bp, bp + 1])):
        ctx, page = new_page(browser, w, scheme, 844)
        page.goto(base + rel, wait_until="load")
        page.evaluate("document.fonts.ready.then(() => true)")
        page.wait_for_timeout(100)
        g = page.evaluate(HERO)
        tag = "%s %s %s, the hero line at %d px" % (engine, scheme, rel, w)
        ok(g is not None, "%s: the line is missing" % tag)
        if g:
            ok(g["sw"] <= g["vw"] + 1, "%s: the page is %d px wide in a %d px window" % (tag, g["sw"], g["vw"]))
            ok(g["text"].startswith("Need work done?") and "Get free quotes from local businesses" in g["text"], "%s: the wording is %r" % (tag, g["text"]))
            ok((g["href"] or "").endswith("request-a-quote.html"), "%s: the link goes to %r" % (tag, g["href"]))
            ok(g["href"] == g["tileHref"], "%s: the line goes to %r but the menu tile to %r" % (tag, g["href"], g["tileHref"]))
            if w <= bp:
                ok(g["shown"], "%s: it should show where the header links are folded away" % tag)
                if g["shown"]:
                    ok(g["link"]["t"] >= g["lastBtn"]["b"], "%s: it is not below the last hero button (%d vs %d)" % (tag, g["link"]["t"], g["lastBtn"]["b"]))
                    ok(g["proof"]["t"] >= g["link"]["b"], "%s: it runs into the list under it (%d vs %d)" % (tag, g["link"]["b"], g["proof"]["t"]))
                    ok(g["link"]["h"] >= 24, "%s: the link is only %d px tall to tap" % (tag, g["link"]["h"]))
                    if w == 390:
                        ok(g["link"]["b"] <= 700, "%s: it ends %d px down, below the first screen" % (tag, g["link"]["b"]))
                        # tapping it reaches the request page (a link written without the leading slash would look for it one folder down on a trade page)
                        try:
                            with page.expect_navigation(wait_until="load", timeout=15000):
                                page.locator(".hero-work a").click()
                            ok(page.url == base + "request-a-quote.html", "%s: tapping it went to %s" % (tag, page.url))
                            ok("quote" in page.title().lower(), "%s: the page it reached is titled %r" % (tag, page.title()))
                        except Exception as e:
                            ok(False, "%s: tapping it failed: %s" % (tag, str(e).splitlines()[0][:160]))
            else:
                ok(not g["shown"], "%s: it should be hidden where the header already shows the link" % tag)
        ctx.close()


def behaviour(browser, base, engine, rel):
    tag = "%s %s" % (engine, rel)
    ctx, page = new_page(browser, 390, "light")
    errors = []
    page.on("pageerror", lambda e: errors.append(str(e)))
    # the home page asks the live app for the founding-spots count; from this local address the live app says no (Chromium and WebKit word it differently): not a header problem
    page.on("console", lambda m: errors.append(m.text) if m.type == "error" and not any(x in m.text for x in IGNORED_CONSOLE) else None)
    try:
        page.goto(base + rel, wait_until="load")
        page.wait_for_timeout(300)
        summary, details = page.locator("header details.navmenu > summary"), page.locator("header details.navmenu")
        is_open = lambda: details.evaluate("d => d.open")

        def ensure_open():
            if not is_open():
                summary.click()
        ok(is_open() is False, "%s: the menu starts open" % tag)
        summary.click()
        ok(is_open() is True, "%s: tapping the button does not open the menu" % tag)
        card = page.evaluate("""() => { const b = document.querySelector('.navmenu-list').getBoundingClientRect(), h = document.querySelector('header').getBoundingClientRect();
            return {l: b.left, r: b.right, t: b.top, headerB: h.bottom, vw: document.documentElement.clientWidth}; }""")
        ok(card["l"] >= 0 and card["r"] <= card["vw"], "%s: the open menu runs off the screen: %s" % (tag, card))
        ok(card["t"] >= card["headerB"], "%s: the open menu sits over the header" % tag)
        for i in range(page.locator(".navmenu-list a").count()):
            bx = page.locator(".navmenu-list a").nth(i).bounding_box()
            ok(bx and bx["height"] >= 40 and bx["x"] >= 0 and bx["x"] + bx["width"] <= 390 and bx["y"] + bx["height"] <= 800, "%s: link %d in the menu is hard to tap or off screen: %s" % (tag, i, bx))
        tile = page.locator(".navmenu-work a")
        tile_text = tile.inner_text() if tile.count() == 1 else None
        ok(tile_text is not None and NEW_LABEL in tile_text and TILE_SUB in tile_text, "%s: the quote tile text is wrong: %r" % (tag, tile_text))
        page.keyboard.press("Escape")
        ok(is_open() is False, "%s: Escape does not close the menu" % tag)
        ok(page.evaluate("document.activeElement && document.activeElement.tagName") == "SUMMARY", "%s: after Escape the focus is not back on the button" % tag)
        ensure_open()
        spot = page.evaluate(QUIET_SPOT)
        ok(spot is not None, "%s: no safe spot found for the outside tap" % tag)
        if spot:
            page.mouse.click(spot[0], spot[1])
            ok(is_open() is False, "%s: a tap outside does not close the menu" % tag)
        # an in-page link: the menu closes and the page moves
        ensure_open()
        links = page.locator(".navmenu-list li:not(.navmenu-work) a")
        inpage = [i for i in range(links.count()) if (links.nth(i).get_attribute("href") or "").startswith("#")]
        ok(bool(inpage), "%s: no in-page link in the menu to test" % tag)
        if inpage:
            target = links.nth(inpage[0]).get_attribute("href")
            links.nth(inpage[0]).click()
            page.wait_for_timeout(400)
            ok(is_open() is False, "%s: tapping %s leaves the menu open" % (tag, target))
            ok(page.evaluate("window.scrollY") > 100, "%s: tapping %s did not scroll the page" % (tag, target))
        # the quote tile reaches the request page
        ensure_open()
        with page.expect_navigation(wait_until="load", timeout=15000):
            page.locator(".navmenu-work a").click()
        ok(page.url.endswith("/request-a-quote.html"), "%s: the quote tile went to %s" % (tag, page.url))
        ok("quote" in page.title().lower(), "%s: the request page title is %r" % (tag, page.title()))
    except Exception as e:  # one broken page must not hide the others
        ok(False, "%s: the menu test stopped: %s" % (tag, str(e).splitlines()[0][:160]))
    ok(not errors, "%s: console errors: %s" % (tag, errors[:2]))
    ctx.close()


def main():
    from playwright.sync_api import sync_playwright

    texts, bps = {}, {}
    for rel in PAGES:
        t = (ROOT / rel).read_text(encoding="utf-8")
        texts[rel] = t
        found = BP_RE.findall(t)
        ok(len(found) == 1, "%s: expected one menu breakpoint in the CSS, found %d" % (rel, len(found)))
        bps[rel] = int(found[0]) if len(found) == 1 else 880
        ok(t.count('<details class="navmenu">') == 1, "%s: expected one menu <details>" % rel)
        ok('<script src="/nav.js" defer></script>' in t, "%s: nav.js is not loaded" % rel)
        ok(OLD_LABEL not in t, "%s: still says %r" % (rel, OLD_LABEL))
        ok(t.count(NEW_LABEL) == 3, "%s: %r should appear 3 times (header link, menu tile, the line under the hero buttons), found %d" % (rel, NEW_LABEL, t.count(NEW_LABEL)))
        ok(t.count('<p class="hero-work">') == 1, "%s: expected one hero line under the buttons" % rel)
        hero_bp = HERO_BP_RE.findall(t)
        ok(len(hero_bp) == 1 and len(found) == 1 and int(hero_bp[0]) == int(found[0]),
           "%s: the hero line should appear at the same width the header links fold away (%s), found %s" % (rel, found, hero_bp))
    ok("Get a free quote" not in texts["index.html"] and TILE_SUB in texts["index.html"], "index.html: the footer line should offer %r" % TILE_SUB)
    ok((ROOT / "nav.js").exists(), "nav.js is missing")

    handler = functools.partial(http.server.SimpleHTTPRequestHandler, directory=str(ROOT))
    handler.log_message = lambda *a, **k: None
    httpd = socketserver.TCPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    base = "http://127.0.0.1:%d/" % httpd.server_address[1]

    with sync_playwright() as p:
        for engine, scheme in (("webkit", "light"), ("chromium", "dark")):
            browser = getattr(p, engine).launch()
            for rel in PAGES:
                geometry(browser, base, engine, scheme, rel, bps[rel])
            for rel in PAGES:
                hero_link(browser, base, engine, scheme, rel, bps[rel])
            for rel in PAGES:
                behaviour(browser, base, engine, rel)
            # the two lists agree (once per page, in the first engine)
            if engine == "webkit":
                for rel in PAGES:
                    ctx, page = new_page(browser, 390, "light")
                    page.goto(base + rel, wait_until="load")
                    lists = page.evaluate(LISTS)
                    ok(lists["header"][:-1] == lists["menu"], "%s: the menu links differ from the header links: %s vs %s" % (rel, lists["menu"], lists["header"][:-1]))
                    ok(len(lists["header"]) >= 2 and len(lists["tile"]) == 1 and lists["header"][-1][0] == lists["tile"][0][0] and lists["header"][-1][1] == NEW_LABEL,
                       "%s: the last header link and the menu tile should be the same page: %s vs %s" % (rel, lists["header"][-1:], lists["tile"]))
                    ctx.close()
            browser.close()
        # without nav.js the button still opens and closes the menu
        browser = p.chromium.launch()
        ctx = browser.new_context(viewport={"width": 390, "height": 800})
        page = ctx.new_page()
        page.route("**/*", lambda r: r.abort() if any(x in r.request.url for x in BLOCKED + ("nav.js",)) else r.continue_())
        page.goto(base + "index.html", wait_until="load")
        page.locator("header details.navmenu > summary").click()
        ok(page.evaluate("document.querySelector('details.navmenu').open") is True, "without nav.js: the button does not open the menu")
        page.locator("header details.navmenu > summary").click()
        ok(page.evaluate("document.querySelector('details.navmenu').open") is False, "without nav.js: the button does not close the menu")
        ctx.close()
        browser.close()
    httpd.shutdown()

    if problems:
        print("FAIL: %d problems in %d checks" % (len(problems), checks[0]))
        sys.exit(1)
    print("PASS: %d checks: %d pages, the header, its menu and the hero line under the buttons hold from 320 to 1440 px in WebKit and Chromium, and the quote link says %r" % (checks[0], len(PAGES), NEW_LABEL))


main()
