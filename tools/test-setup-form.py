#!/usr/bin/env python3
"""The done-for-you set-up form (setup.html, served at /setup; 20 Nov 2026, phase 1 of founder-notes/done-for-you-onboarding-2026-11-20/SPEC.md).

    $PY tools/test-setup-form.py                 run the checks (Playwright; the app's endpoint is answered by this test, every other host is blocked and recorded)
    $PY tools/test-setup-form.py --selftest      breaks a temp copy of the page on purpose, many ways, and shows these checks catch each
    $PY tools/test-setup-form.py --shots DIR     saves the form at 375 and 1280 wide (top, services, uploads, consent, thank-you) for the owner

What it checks: every field has a label tied to it and is 16 px or more (so a phone does not zoom); the hidden spam field is hidden from screen readers and from the Tab key; the trade
list is the app's sign-up list (#lockIndustry in the app repo's index.html, read with git from its origin/main) and the starter services are the app's DEFAULT_CATALOG; the limits are
the server's (api/_setuprequest.js); choosing a trade fills in its services and never overwrites the person's own; the logo is made a 200 px PNG on the device and an SVG or a file over
5 MB is refused; a customer list over 1 MB or 2,000 rows is refused before it is sent; the page checks the fields before sending (and puts the cursor on the first problem), sends only the
keys the server accepts, and shows a problem the server names next to its field; the thank-you; the "paused" switch; that the page loads no pixel and asks no third party for anything; the
bank-details line above the button; the consent ticks; the plain-English rules (no em dash, no exclamation mark, no "tax invoice", no "monthly"); and no sideways scroll at 320, 375 and 1280,
light and dark.
"""
import base64, functools, http.server, json, os, pathlib, re, shutil, socketserver, struct, subprocess, sys, tempfile, threading, zlib

ROOT = pathlib.Path(os.environ.get("KEPT_SETUPFORM_ROOT") or pathlib.Path(__file__).resolve().parent.parent)
def _app_repo():
    """The app repo: KEPT_APP_REPO, else jobs-app beside this site's clone (found through git, so it works from a worktree too)."""
    if os.environ.get("KEPT_APP_REPO"):
        return pathlib.Path(os.environ["KEPT_APP_REPO"])
    try:
        common = subprocess.run(["git", "-C", str(pathlib.Path(__file__).resolve().parent), "rev-parse", "--git-common-dir"], capture_output=True, text=True, check=True).stdout.strip()
        return (pathlib.Path(__file__).resolve().parent / common).resolve().parent.parent / "jobs-app"
    except Exception:
        return pathlib.Path(__file__).resolve().parent.parent.parent / "jobs-app"


APP_REPO = _app_repo()
APP_REFS = [r for r in (os.environ.get("KEPT_APP_REF"), "origin/main", "setup-form-phase1") if r]   # the app's sign-up list is on origin/main; the server helper may only be on the branch
ENDPOINT = "https://app.keptsoftware.com.au/api/leads"
PAGE = "setup.html"


class Quiet(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *a, **k):
        pass


def app_file(rel):
    """A file of the app repo at the first ref that has it (git show: the clone's working tree is never read). None when there is no app repo here."""
    for ref in APP_REFS:
        try:
            return subprocess.run(["git", "-C", str(APP_REPO), "show", "%s:%s" % (ref, rel)], capture_output=True, text=True, check=True).stdout
        except Exception:
            continue
    return None


def png(w, h):
    rows = b"".join(b"\x00" + bytes((11, 122, 67, 255)) * w for _ in range(h))
    chunk = lambda k, d: struct.pack(">I", len(d)) + k + d + struct.pack(">I", zlib.crc32(k + d) & 0xffffffff)
    return b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0)) + chunk(b"IDAT", zlib.compress(rows)) + chunk(b"IEND", b"")


class Run:
    def __init__(self):
        self.problems, self.n = [], 0

    def check(self, ok, what):
        self.n += 1
        if not ok:
            self.problems.append(what)


def serve(root):
    handler = functools.partial(Quiet, directory=str(root))
    httpd = socketserver.TCPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    return httpd, "http://127.0.0.1:%d/" % httpd.server_address[1]


GOOD = dict(suName="Jess Nguyen", suEmail="jess@brightside.example", suEmail2="jess@brightside.example", suMobile="0412 345 678", suBizName="Bright Side Cleaning", suAbn="51 824 753 556",
            suAddress="4 Example Pde, Redbank QLD 4301", suPostcode="4301")


def open_page(browser, base, width=375, height=812, scheme="light", answer=None, html=None):
    """The page, with the app's endpoint answered by `answer` (status, body) and every other outside request recorded and refused."""
    ctx = browser.new_context(viewport={"width": width, "height": height}, color_scheme=scheme, locale="en-AU")
    page = ctx.new_page()
    page.outside, page.sent, page.errors = [], [], []
    page.on("pageerror", lambda e: page.errors.append(str(e)))
    page.on("console", lambda m: page.errors.append(m.text) if m.type == "error" else None)

    def route(r):
        url = r.request.url
        if url.startswith(base):
            if html is not None and url.split("?")[0].endswith(PAGE):
                return r.fulfill(status=200, content_type="text/html", body=html)
            return r.continue_()
        if url == ENDPOINT and r.request.method == "POST":
            page.sent.append(json.loads(r.request.post_data or "{}"))
            st, body = answer or (200, {"ok": True})
            return r.fulfill(status=st, content_type="application/json", body=json.dumps(body), headers={"Access-Control-Allow-Origin": "*"})
        if url == ENDPOINT and r.request.method == "OPTIONS":
            return r.fulfill(status=204, headers={"Access-Control-Allow-Origin": "*", "Access-Control-Allow-Headers": "Content-Type", "Access-Control-Allow-Methods": "POST"})
        page.outside.append(url)
        return r.abort()
    page.route("**/*", route)
    page.set_default_timeout(5000)   # everything here is local: a wait this long has failed
    page.clock.install()
    page.goto(base + PAGE, wait_until="load")
    return page


def fill_good(page, trade="cleaning"):
    for k, v in GOOD.items():
        page.fill("#" + k, v)
    page.select_option("#suTrade", trade)
    page.check('input[name="gst"][value="yes"]')
    page.check('input[name="plan"][value="solo"]')
    for t in ("suConsentAuth", "suConsentList", "suConsentPrivacy"):
        page.check("#" + t)


def submit(page):
    page.clock.fast_forward(6000)
    page.click("#suSubmit")
    page.wait_for_timeout(300)


def run(root):
    from playwright.sync_api import sync_playwright
    R = Run()
    html = (root / PAGE).read_text(encoding="utf-8")
    index_app = app_file("index.html")
    app_js = app_file("app.js")
    helper = app_file("api/_setuprequest.js")
    httpd, base = serve(root)
    try:
        # ---- the page as text
        R.check("fbq(" not in html and "facebook.com/tr" not in html and "connect.facebook.net" not in html, "setup.html carries the Meta Pixel (it must not: the page takes other people's details)")
        R.check(not re.search(r"<script[^>]+src=\"https?://", html), "setup.html loads a script from another site")
        R.check('<script src="/attribution.js" defer></script>' in html, "setup.html should load the site's own attribution.js")
        R.check("var SETUP_FORM_OPEN = true;" in html, "the rollback switch SETUP_FORM_OPEN is there and on")
        R.check("var ENDPOINT = 'https://app.keptsoftware.com.au/api/leads';" in html, "the form posts to the app's leads endpoint")
        R.check(html.count("Don't put bank details or passwords in this form. You'll add bank details in the app yourself.") == 1, "the bank-details line is on the page once")
        visible = re.sub(r"<script.*?</script>|<style.*?</style>|<!--.*?-->", " ", html, flags=re.S)
        visible_text = re.sub(r"<[^>]+>", " ", visible)
        R.check("\u2014" not in visible_text and "\u2013" not in visible_text, "an em or en dash in the page's text")
        R.check("!" not in visible_text, "an exclamation mark in the page's text")
        R.check(not re.search(r"(?i)tax invoice|monthly", visible_text), "'tax invoice' or 'monthly' in the page's text")
        for tick in ("I'm authorised to set up Kept for this business, and the details here are correct.",
                     "If I send a customer list, it's my business's own records. I'm allowed to give it to Kept so Kept can help load it into my account, and I've told my customers (for example in my own privacy notice) that I use software providers to run my business.",
                     "I've read how Kept handles this form (above) and the"):
            R.check(tick in html, "a consent tick's words changed: %s" % tick[:60])
        for must in ("It's stored in Sydney, Australia.", "nothing is kept longer than 30 days after you send it", "We never contact your customers and never use their details for anything else."):
            R.check(must in html, "the handling text lost: %s" % must)
        got = re.findall(r'<option value="([a-z_]+)"', re.search(r'<select id="suTrade"[^>]*>(.*?)</select>', html, re.S).group(1))
        trades = got
        if index_app is not None:
            m = re.search(r'<select id="lockIndustry">(.*?)</select>', index_app, re.S)
            want = re.findall(r'<option value="([a-z_]+)"', re.sub(r"<!--.*?-->", "", m.group(1), flags=re.S))
            R.check(got == want, "the trade list %s is not the app's sign-up list %s" % (got, want))
            trades = want
        else:
            print("note: no app repo at %s, the trade list was not compared" % APP_REPO)
        starters = re.search(r"var STARTERS = \{(.*?)\n  \};", html, re.S).group(1)
        keys = re.findall(r"^    ([a-z_]+): \[", starters, re.M)
        R.check(keys == trades, "the starter lists %s are not one per trade, in the trade list's order %s" % (keys, trades))
        if app_js is not None:
            cat = app_js[app_js.index("const DEFAULT_CATALOG={"):]
            for trade in trades:
                if not re.search(r"\n  %s:\[" % trade, cat) or not re.search(r"\n    %s: \[" % trade, html):
                    R.check(False, "the trade %s has no starter list in the app's DEFAULT_CATALOG or on the page" % trade)
                    continue
                block = re.search(r"\n  %s:\[(.*?)\]" % trade, cat, re.S).group(1)
                rows = [(a.replace(" \u2014 ", ", "), b.replace(" \u2014 ", ", "), c, float(d)) for a, b, c, d in re.findall(r"\{name:'([^']*)',description:'([^']*)',rateType:'(\w+)',rate:([\d.]+)\}", block)]
                mine = re.search(r"\n    %s: \[(.*?)\](?:,|\n)" % trade, html, re.S).group(1)
                ours = [(a, b, c, float(d)) for a, b, c, d in re.findall(r"\{ name: '([^']*)', description: '([^']*)', rateType: '(\w+)', rate: ([\d.]+) \}", mine)]
                R.check(rows == ours, "the starter services for %s are not the app's DEFAULT_CATALOG: %s vs %s" % (trade, ours, rows))
        if helper is not None:
            num = lambda k: int(re.search(r"\b%s: (\d+)," % k, helper).group(1))
            lim = re.search(r"var LIMITS = \{([^}]*)\}", html).group(1)
            for page_key, srv_key in (("logo", "logo"), ("csvBytes", "csvBytes"), ("csvRows", "csvRows"), ("services", "services")):
                R.check(re.search(r"\b%s: %d\b" % (page_key, num(srv_key)), lim) is not None, "the page's %s limit is not the server's %d" % (page_key, num(srv_key)))
            accepted = set(re.findall(r"'([A-Za-z0-9]+)'", re.search(r"const ACCEPTED_KEYS = \[(.*?)\];", helper, re.S).group(1)))
        else:
            accepted = None
            print("note: api/_setuprequest.js not found in the app repo, the limits were not compared")

        with sync_playwright() as p:
          browser = p.chromium.launch()
          try:
            browser_checks(R, browser, base, html, accepted)
          except Exception as e:   # a break that makes a later step impossible (the form already gone, say) is a failure, not a crash
            R.check(False, "the checks could not go on: %s" % str(e).splitlines()[0][:200])
          browser.close()
    finally:
        httpd.shutdown()
        httpd.server_close()
    return R


def browser_checks(R, browser, base, html, accepted):
    if True:   # (the body keeps the indent it had inside run())
            # ---- fields, labels, sizes, the hidden field
            page = open_page(browser, base)
            info = page.evaluate("""() => {
              const out = { unlabelled: [], small: [], hp: null };
              document.querySelectorAll('#setupForm input, #setupForm select, #setupForm textarea').forEach(el => {
                if (el.closest('.hp-field')) return;
                const named = (el.id && document.querySelector('label[for="' + el.id + '"]')) || el.closest('label');
                if (!named) out.unlabelled.push(el.id || el.name);
                if (el.type !== 'checkbox' && el.type !== 'radio' && el.type !== 'file' && parseFloat(getComputedStyle(el).fontSize) < 16) out.small.push(el.id + ' ' + getComputedStyle(el).fontSize);
              });
              const hp = document.querySelector('.hp-field'), hpIn = hp && hp.querySelector('input');
              out.hp = hp && { hidden: hp.getAttribute('aria-hidden'), tab: hpIn && hpIn.getAttribute('tabindex'), name: hpIn && hpIn.name, left: hp.getBoundingClientRect().right };
              out.h1 = document.querySelectorAll('h1').length;
              return out; }""")
            R.check(info["unlabelled"] == [], "fields without a label: %s" % info["unlabelled"])
            R.check(info["small"] == [], "fields under 16 px (a phone zooms in on them): %s" % info["small"])
            R.check(info["hp"] and info["hp"]["hidden"] == "true" and info["hp"]["tab"] == "-1" and info["hp"]["name"] == "website" and info["hp"]["left"] <= 0, "the hidden spam field is not hidden: %s" % info["hp"])
            R.check(info["h1"] == 1, "one h1")
            nb = page.evaluate("() => document.getElementById('suNoBank').compareDocumentPosition(document.getElementById('suSubmit')) & Node.DOCUMENT_POSITION_FOLLOWING")
            R.check(bool(nb), "the bank-details line must come before the Send button")

            # ---- starter services
            page.select_option("#suTrade", "cleaning")
            names = page.eval_on_selector_all("#svcList .svc input[id^=svcName]", "els => els.map(e => e.value)")
            R.check(names == ["Regular clean (2 bed/1 bath)", "Regular clean (3 bed/2 bath)", "Bond/end-of-lease clean"], "cleaning fills its three services: %s" % names)
            page.select_option("#suTrade", "handyman")
            names = page.eval_on_selector_all("#svcList .svc input[id^=svcName]", "els => els.map(e => e.value)")
            R.check(names[:1] == ["General handyman, per hour"] and len(names) == 3, "a new trade replaces untouched starters: %s" % names)
            page.select_option("#suTrade", "property_maintenance")
            names = page.eval_on_selector_all("#svcList .svc input[id^=svcName]", "els => els.map(e => e.value)")
            R.check(names[:1] == ["Mow and edge, standard block"] and names[-1:] == ["Trailer load to the tip"] and len(names) == 7, "property maintenance fills its seven services: %s" % names)
            page.select_option("#suTrade", "handyman")
            page.fill("#svcList .svc input[id^=svcRate]", "80")
            page.select_option("#suTrade", "lawn_care")
            R.check(page.eval_on_selector_all("#svcList .svc", "els => els.length") == 3, "a trade change must never overwrite services the person changed")
            for _ in range(40):
                if page.is_disabled("#svcAdd"):
                    break
                page.click("#svcAdd")
            R.check(page.eval_on_selector_all("#svcList .svc", "els => els.length") == 30 and page.is_disabled("#svcAdd"), "Add a service stops at 30")
            page.click('#svcList [data-remove]')
            R.check(page.eval_on_selector_all("#svcList .svc", "els => els.length") == 29 and not page.is_disabled("#svcAdd"), "Remove takes a row away")
            R.check(page.evaluate("() => document.activeElement.id") == "svcAdd", "after Remove the cursor is on Add a service, not lost")
            page.context.close()

            # ---- the logo
            page = open_page(browser, base)
            page.set_input_files("#suLogo", files=[{"name": "logo.png", "mimeType": "image/png", "buffer": png(800, 400)}])
            page.wait_for_function("() => !document.getElementById('suLogoPreview').hidden")
            dims = page.evaluate("""() => new Promise(r => { const i = new Image(); i.onload = () => r([i.width, i.height, document.getElementById('suLogoPreview').src.slice(0, 22)]); i.src = document.getElementById('suLogoPreview').src; })""")
            R.check(dims == [200, 100, "data:image/png;base64,"], "the logo is made 200 px across as a PNG: %s" % dims)
            page.set_input_files("#suLogo", files=[{"name": "logo.svg", "mimeType": "image/svg+xml", "buffer": b"<svg xmlns='http://www.w3.org/2000/svg' onload='alert(1)'/>"}])
            page.wait_for_timeout(150)
            R.check(page.inner_text("#suLogoErr") == "Choose a PNG, JPEG or WebP picture." and page.is_hidden("#suLogoPreview"), "an SVG logo is refused: %r" % page.inner_text("#suLogoErr"))
            page.set_input_files("#suLogo", files=[{"name": "big.png", "mimeType": "image/png", "buffer": png(1, 1) + b"\0" * 5300000}])
            page.wait_for_timeout(150)
            R.check("over 5 MB" in page.inner_text("#suLogoErr"), "a logo file over 5 MB is refused: %r" % page.inner_text("#suLogoErr"))

            # ---- the customer list
            page.set_input_files("#suCsv", files=[{"name": "customers.csv", "mimeType": "text/csv", "buffer": b"Name,Phone\r\nSarah,0491 570 156\r\nTom,\"0491\n570 157\"\r\n,\r\n"}])
            page.wait_for_function("() => document.getElementById('suCsvOk').textContent")
            R.check(page.inner_text("#suCsvOk") == "2 rows ready to send.", "a good list is counted as the app reads it: %r" % page.inner_text("#suCsvOk"))
            page.set_input_files("#suCsv", files=[{"name": "big.csv", "mimeType": "text/csv", "buffer": b"Name\n" + b"x" * 1048600}])
            page.wait_for_timeout(150)
            R.check("over 1 MB" in page.inner_text("#suCsvErr") and page.inner_text("#suCsvOk") == "", "a list over 1 MB is refused: %r" % page.inner_text("#suCsvErr"))
            page.set_input_files("#suCsv", files=[{"name": "long.csv", "mimeType": "text/csv", "buffer": b"Name\n" + b"A\n" * 2001}])
            page.wait_for_timeout(200)
            R.check("2,001 rows" in page.inner_text("#suCsvErr"), "a list over 2,000 rows is refused: %r" % page.inner_text("#suCsvErr"))
            page.set_input_files("#suCsv", files=[{"name": "customers.xlsx", "mimeType": "application/octet-stream", "buffer": b"PK\x03\x04"}])
            page.wait_for_timeout(100)
            R.check(".csv file" in page.inner_text("#suCsvErr"), "a spreadsheet file that is not CSV is refused")
            page.context.close()

            # ---- checking before sending
            page = open_page(browser, base)
            submit(page)
            R.check(page.sent == [] and page.evaluate("() => document.activeElement.id") == "suName" and page.inner_text("#suNameErr") == "Please fill in your name.", "an empty form is stopped at the name")
            R.check(page.get_attribute("#suName", "aria-invalid") == "true", "the field with the problem is marked invalid")
            fill_good(page)
            page.fill("#suEmail2", "jess@brightside.exampel")
            submit(page)
            R.check(page.sent == [] and page.evaluate("() => document.activeElement.id") == "suEmail2", "two different emails are stopped")
            page.fill("#suEmail2", GOOD["suEmail2"])
            page.fill("#suAbn", "51 824 753 557")
            submit(page)
            R.check(page.sent == [] and "ABN does not check out" in page.inner_text("#suAbnErr"), "a wrong ABN is stopped")
            page.fill("#suAbn", GOOD["suAbn"])
            page.fill("#suMobile", "07 3123 4567")
            submit(page)
            R.check(page.sent == [] and page.evaluate("() => document.activeElement.id") == "suMobile", "a landline as the mobile is stopped")
            page.fill("#suMobile", GOOD["suMobile"])
            page.uncheck("#suConsentList")
            submit(page)
            R.check(page.sent == [] and page.evaluate("() => document.activeElement.id") == "suConsentList", "a missing consent tick is stopped")
            page.check("#suConsentList")
            page.fill("#svcList .svc input[id^=svcRate] >> nth=1", "12.345")
            submit(page)
            R.check(page.sent == [] and page.inner_text("#svcErr").startswith("Service 2:") and page.evaluate("() => document.activeElement.id").startswith("svcName"), "a bad price is stopped at its row")
            page.fill("#svcList .svc input[id^=svcRate] >> nth=1", "150")
            page.fill("#suHp", "")
            submit(page)
            R.check(len(page.sent) == 1, "a good form is sent once: %d" % len(page.sent))
            body = page.sent[0] if page.sent else {}
            R.check(body.get("kind") == "setup" and body.get("v") == 1 and body.get("industry") == "cleaning" and body.get("plan") == "solo" and body.get("gst") == "yes", "the body says what it is: %s" % {k: body.get(k) for k in ("kind", "v", "industry", "plan")})
            R.check(isinstance(body.get("elapsedMs"), (int, float)) and body["elapsedMs"] >= 4000, "the time since the page opened is sent: %s" % body.get("elapsedMs"))
            R.check(body.get("website") == "", "the hidden field is sent empty")
            R.check([s["name"] for s in body.get("services", [])] == ["Regular clean (2 bed/1 bath)", "Regular clean (3 bed/2 bath)", "Bond/end-of-lease clean"] and body["services"][1]["rate"] == "150", "the services are sent")
            R.check(all(isinstance(body.get("consent", {}).get(k), str) for k in ("authorised", "customerList", "privacy")), "each tick is sent with its time: %s" % body.get("consent"))
            if accepted is not None:
                R.check(sorted(set(body) - accepted) == [], "the page sends keys the server does not read: %s" % sorted(set(body) - accepted))
            R.check(not re.search(r"(?i)bank|bsb|password|tfn", json.dumps(sorted(body))), "the body has a bank or password key")
            done = page.evaluate("() => ({ form: document.getElementById('setupForm').hidden, done: !document.getElementById('suDone').hidden, focus: document.activeElement.id, text: document.getElementById('suDone').innerText })")
            R.check(done["form"] and done["done"] and done["focus"] == "suDone", "the thank-you replaces the form and takes the focus: %s" % done)
            R.check("Elliot will check your details and get back to you, usually within one working day" in done["text"], "the thank-you words")
            R.check(page.outside == [], "the page asked another site for something: %s" % page.outside)
            R.check(page.errors == [], "errors on the page: %s" % page.errors)
            page.context.close()

            # ---- a problem the server names, and a server that cannot be reached
            page = open_page(browser, base, answer=(400, {"ok": False, "field": "mobile", "error": "That mobile number does not look right."}))
            fill_good(page)
            submit(page)
            R.check(page.inner_text("#suMobileErr") == "That mobile number does not look right." and page.evaluate("() => document.activeElement.id") == "suMobile" and not page.is_hidden("#setupForm"), "a problem the server names is shown at its field")
            R.check(page.is_enabled("#suSubmit") and page.inner_text("#suSubmit") == "Send my details", "the button comes back after a refusal")
            page.context.close()
            page = open_page(browser, base, answer=(429, {"ok": False, "error": "We're catching up on set-ups. Please try again tomorrow."}))
            fill_good(page)
            submit(page)
            R.check(page.inner_text("#suStatus") == "We're catching up on set-ups. Please try again tomorrow." and not page.is_hidden("#setupForm"), "a refusal without a field is said under the button")
            page.context.close()

            # ---- the switch
            page = open_page(browser, base, html=html.replace("var SETUP_FORM_OPEN = true;", "var SETUP_FORM_OPEN = false;"))
            R.check(page.is_hidden("#setupForm") and page.is_visible("#paused"), "SETUP_FORM_OPEN false shows the paused card instead of the form")
            page.context.close()

            # ---- no sideways scroll
            for scheme in ("light", "dark"):
                for w in (320, 375, 1280):
                    page = open_page(browser, base, width=w, scheme=scheme)
                    page.select_option("#suTrade", "pressure_washing")
                    page.check("#suRunOther")
                    over = page.evaluate("() => document.documentElement.scrollWidth - document.documentElement.clientWidth")
                    R.check(over <= 0, "setup.html scrolls sideways by %d px at %d (%s)" % (over, w, scheme))
                    page.context.close()


def shots(root, out):
    from playwright.sync_api import sync_playwright
    out = pathlib.Path(out)
    out.mkdir(parents=True, exist_ok=True)
    httpd, base = serve(root)
    try:
        with sync_playwright() as p:
            browser = p.chromium.launch()
            for w, h in ((375, 812), (1280, 900)):
                page = open_page(browser, base, width=w, height=h)
                page.screenshot(path=str(out / ("form-%d-1-top.png" % w)))
                fill_good(page)
                page.check('input[name="run"][value="paper"]')
                page.check('input[name="staff"][value="1-3"]')
                page.set_input_files("#suLogo", files=[{"name": "logo.png", "mimeType": "image/png", "buffer": png(300, 300)}])
                page.set_input_files("#suCsv", files=[{"name": "customers.csv", "mimeType": "text/csv", "buffer": ("Name,Phone\r\n" + "".join("Client %d,0491 570 %03d\r\n" % (i, i) for i in range(42))).encode()}])
                page.wait_for_function("() => document.getElementById('suCsvOk').textContent && !document.getElementById('suLogoPreview').hidden")
                for name, sel in (("2-services", "#hSvc"), ("3-uploads", "#hFiles"), ("4-consent", "#hSend")):
                    page.eval_on_selector(sel, "e => e.closest('section').scrollIntoView({block: 'start'})")
                    page.wait_for_timeout(100)
                    page.screenshot(path=str(out / ("form-%d-%s.png" % (w, name))))
                submit(page)
                page.screenshot(path=str(out / ("form-%d-5-thank-you.png" % w)))
                page.context.close()
            browser.close()
    finally:
        httpd.shutdown()
        httpd.server_close()
    print("saved to %s" % out)


# --selftest: each break is made in a temp copy of setup.html; the checks must fail on every one. (what, the exact text, what replaces it)
BREAKS = [
    ("the Meta Pixel is added", "  <script src=\"/attribution.js\" defer></script>\n", "  <script>fbq('init', '841447128961693');</script>\n  <script src=\"/attribution.js\" defer></script>\n"),
    ("the honeypot is visible to screen readers", '<div class="hp-field" aria-hidden="true">', '<div class="hp-field">'),
    ("a field loses its label", '<label for="suBizName">Business name</label>', '<span>Business name</span>'),
    ("fields shrink to 15 px", "font-family:inherit;font-size:16px;background:var(--field)", "font-family:inherit;font-size:15px;background:var(--field)"),
    ("a trade the app does not offer", '<option value="handyman">Handyman</option>', '<option value="handyman">Handyman</option>\n            <option value="electrician">Electrician</option>'),
    ("a starter price drifts from the app", "rateType: 'flat', rate: 480 }", "rateType: 'flat', rate: 450 }"),
    ("the newest trade is left out", '            <option value="property_maintenance">Property maintenance</option>\n', ""),
    ("a property maintenance starter drifts", "description: 'Includes a downpipe check', rateType: 'flat', rate: 150 }", "description: 'Includes a downpipe check', rateType: 'flat', rate: 140 }"),
    ("a trade loses its starter list", "    property_maintenance: [\n", "    propertyMaintenance: [\n"),
    ("the logo is sent at full size", "resizeToPng(f, 200).then(", "resizeToPng(f, 2000).then("),
    ("an SVG logo is taken", "if (['image/png', 'image/jpeg', 'image/webp'].indexOf(f.type) < 0)", "if (false)"),
    ("the 1 MB check is gone", "if (f.size > LIMITS.csvBytes) {", "if (false) {"),
    ("the 2,000-row check is gone", "if (rows > LIMITS.csvRows) {", "if (false) {"),
    ("the page's limit drifts from the server's", "csvRows: 2000,", "csvRows: 5000,"),
    ("the ABN is not checked", "if (d.abn && !abnOk(d.abn)) return", "if (false) return"),
    ("a missing tick goes through", "if (!d.consent.customerList) return", "if (false) return"),
    ("the time on the page is not sent", "elapsedMs: Date.now() - OPENED,", "elapsedMs: 0,"),
    ("a trade change wipes the person's services", "if (svcTouched) return;", ""),
    ("the bank-details line is gone", "<p class=\"nobank\" id=\"suNoBank\">Don't put bank details or passwords in this form. You'll add bank details in the app yourself.</p>", "<p class=\"nobank\" id=\"suNoBank\"></p>"),
    ("the page sends a key the server does not read", "kind: 'setup', v: 1,", "kind: 'setup', v: 1, bankName: '',"),
    ("a server problem is not shown at its field", "if (x.r && x.r.field && FIELD[x.r.field]) showProblem(", "if (false) showProblem("),
    ("an em dash in the text", "Both are optional.", "Both are optional \u2014 really."),
    ("a wide element", "<main class=\"wrap\">", "<main class=\"wrap\"><div style=\"width:900px;height:2px\"></div>"),
    ("the switch is gone", "if (!SETUP_FORM_OPEN) { form.hidden = true; $('paused').hidden = false; return; }", ""),
    ("the thank-you does not take the focus", "$('suDone').hidden = false; $('suDone').focus();", "$('suDone').hidden = false;"),
    ("a third-party font", "<link rel=\"preload\" href=\"/fonts/schibsted-grotesk-latin.woff2\"", "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=Inter\">\n<link rel=\"preload\" href=\"/fonts/schibsted-grotesk-latin.woff2\""),
]


def main():
    if "--shots" in sys.argv:
        shots(ROOT, sys.argv[sys.argv.index("--shots") + 1])
        return
    R = run(ROOT)
    for p in R.problems:
        print("FAIL  " + p)
    if R.problems:
        print("FAIL: %d of %d checks" % (len(R.problems), R.n))
        sys.exit(1)
    print("PASS: %d checks on setup.html" % R.n)
    if "--selftest" not in sys.argv:
        return
    missed = []
    for what, old, new in BREAKS:
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="kept-setupform-"))
        try:
            for item in ("setup.html", "attribution.js", "fonts", "icons"):
                src = ROOT / item
                (shutil.copytree if src.is_dir() else shutil.copy)(src, tmp / item)
            body = (tmp / PAGE).read_text(encoding="utf-8")
            if body.count(old) != 1:
                print("%-52s CANNOT BREAK (the text occurs %d times: update this test)" % (what, body.count(old)))
                missed.append(what)
                continue
            (tmp / PAGE).write_text(body.replace(old, new), encoding="utf-8")
            found = run(tmp).problems
            print("%-52s %s" % (what, "CAUGHT" if found else "NOT CAUGHT"))
            if not found:
                missed.append(what)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    if missed:
        print("SELFTEST FAILED: " + ", ".join(missed))
        sys.exit(1)
    print("SELFTEST OK: all %d deliberate breaks were caught" % len(BREAKS))


if __name__ == "__main__":
    main()
