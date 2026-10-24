#!/usr/bin/env python3
"""No page of the site scrolls sideways, at phone, tablet and desktop widths, in light and dark.

    $PY tools/test-no-sideways-scroll.py             run the checks (Playwright; Meta and Google hosts are blocked)
    $PY tools/test-no-sideways-scroll.py --selftest  also add a too-wide element to a temp copy and confirm it is caught

Why: on 24 October 2026 a longer price in the homepage comparison table made the homepage 391 px wide on a 375 px phone. Each edit looked fine on its own and
the comparison-page tests only look at their own pages, so nothing noticed until a screenshot check. This looks at every page, at 320, 375, 414, 768 and 1280 px,
with the optional "What reviewers say" section opened, because that is where competitor text lands.
"""
import functools, http.server, os, pathlib, shutil, socketserver, sys, tempfile, threading

ROOT = pathlib.Path(os.environ.get("KEPT_SCROLL_ROOT") or pathlib.Path(__file__).resolve().parent.parent)
WIDTHS = [320, 375, 414, 768, 1280]


def pages(root):
    return sorted(str(p.relative_to(root)) for p in root.rglob("*.html") if p.relative_to(root).parts[0] not in ("tools", ".git", "node_modules"))


def run(root):
    from playwright.sync_api import sync_playwright
    handler = functools.partial(http.server.SimpleHTTPRequestHandler, directory=str(root))
    handler.log_message = lambda *a, **k: None
    httpd = socketserver.TCPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    base = "http://127.0.0.1:%d/" % httpd.server_address[1]
    problems, checked = [], 0
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for scheme in ("light", "dark"):
            for w in WIDTHS:
                ctx = browser.new_context(viewport={"width": w, "height": 800}, color_scheme=scheme)
                page = ctx.new_page()
                page.route("**/*", lambda r: r.abort() if any(x in r.request.url for x in ("facebook", "google", "googletagmanager")) else r.continue_())
                for rel in pages(root):
                    page.goto(base + rel, wait_until="load")
                    page.wait_for_timeout(120)
                    page.evaluate("document.querySelectorAll('details').forEach(d => d.open = true)")
                    wide = page.evaluate("""() => { const vw = document.documentElement.clientWidth;
                        const over = document.documentElement.scrollWidth - vw;
                        if (over <= 1) return null;
                        const names = []; document.querySelectorAll('body *').forEach(e => { const r = e.getBoundingClientRect();
                            if (r.width > 0 && r.right > vw + 1 && getComputedStyle(e).position !== 'absolute' && names.length < 3) names.push(e.tagName.toLowerCase() + (e.id ? '#' + e.id : '') + ' right ' + Math.round(r.right)); });
                        return {over: over, names: names}; }""")
                    checked += 1
                    if wide:
                        problems.append("%s at %d px (%s): %d px too wide %s" % (rel, w, scheme, wide["over"], wide["names"]))
                ctx.close()
        browser.close()
    httpd.shutdown()
    return problems, checked


def main():
    problems, checked = run(ROOT)
    for p in problems:
        print("FAIL  " + p)
    if problems:
        print("FAIL: %d page views scroll sideways (of %d)" % (len(problems), checked))
        sys.exit(1)
    print("PASS: %d page views (%d pages x %d widths x light and dark), none scroll sideways" % (checked, len(pages(ROOT)), len(WIDTHS)))
    if "--selftest" not in sys.argv:
        return
    tmp = pathlib.Path(tempfile.mkdtemp(prefix="kept-scroll-"))
    try:
        for rel in pages(ROOT):
            dest = tmp / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, dest)
        for sub in ("fonts", "icons", "images", "videos"):
            if (ROOT / sub).is_dir():
                shutil.copytree(ROOT / sub, tmp / sub)
        victim = tmp / "index.html"
        text = victim.read_text(encoding="utf-8")
        victim.write_text(text.replace("</body>", '<div id="too-wide" style="width:600px;height:4px;background:red"></div></body>', 1), encoding="utf-8")
        found, _ = run(tmp)
        print("a 600 px element added to the homepage: %s" % ("CAUGHT" if any(f.startswith("index.html") for f in found) else "NOT CAUGHT"))
        if not any(f.startswith("index.html") for f in found):
            sys.exit(1)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print("SELFTEST OK: a page that is too wide is caught")


if __name__ == "__main__":
    main()
