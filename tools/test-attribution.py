#!/usr/bin/env python3
"""Browser tests for attribution.js, the website's "which ad brought this visitor" script.

Run it with the app repo's Python, which has Playwright and a cached headless Chromium
(there is no Node on this machine):

  PY="/Users/elliotlangham/Documents/Lawn envy revamp/jobs-app/tools/demo-capture/.venv/bin/python"
  "$PY" tools/test-attribution.py              # the suite; prints PASS/FAIL per check, exit 1 on any FAIL
  "$PY" tools/test-attribution.py --selftest   # proves the suite can fail: breaks attribution.js
                                               # (and the contact form) on purpose, 11 ways, and
                                               # checks the suite goes red each time
  "$PY" tools/test-attribution.py --only 4,6   # just those case numbers (while developing)
  "$PY" tools/test-attribution.py --browser webkit   # the same suite in WebKit (iPhone Safari's engine)

How it works: the site folder is served from a local threaded http.server on a free port. Every
request to anywhere else is aborted (Facebook, Google Tag Manager, fonts ...), and requests to
https://app.keptsoftware.com.au/** are answered by a stub (a tiny page, and {"ok":true} for
POST /api/leads, recording the body). A stub window.fbq is injected before any page script runs,
so the pages' own pixel snippet leaves it alone; it records every call in window.__fbq and also
sends it to Python, which means events survive the page navigating away. Nothing waits on a fixed
sleep: every wait polls a real, observable state (storage, the URL, an event arriving) with a
deadline. Python 3.9 compatible.
"""
import argparse
import functools
import http.server
import json
import re
import sys
import threading
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

from playwright.sync_api import sync_playwright

SITE = Path(__file__).resolve().parent.parent
ATTR_JS = SITE / "attribution.js"
APP = "https://app.keptsoftware.com.au"

TAGS_QS = "utm_source=facebook&utm_medium=paid_social&utm_campaign=lawn_time&utm_content=reel1&gclid=abc"
TAGS = {"utm_source": "facebook", "utm_medium": "paid_social", "utm_campaign": "lawn_time",
        "utm_content": "reel1", "gclid": "abc"}
# What a decorated app link gets after its own parameters, for a visit that landed on "/".
SUFFIX = TAGS_QS + "&kl=%2F"
VALUE_OK = re.compile(r"^[A-Za-z0-9_.~+%:/-]{1,100}$")

HOME_PAGES = ["/", "/vs-jobber.html", "/vs-servicem8.html", "/vs-yardbook.html", "/vs-zenmaid.html", "/vs-fergus.html", "/vs-sortscape.html",
              "/lawn-care/", "/wash/", "/clean/", "/handyman/", "/card/", "/request-a-quote.html"]

# Injected into every page before its own scripts. Stubs window.fbq (so Meta's snippet does nothing
# and nothing is sent to Facebook) and reports every fbq call and every click to Python.
INIT_STUB = r"""
(function () {
  var send = function (kind, data) {
    try { window.__keptSink(kind, JSON.stringify(data)); } catch (e) {}
  };
  window.__fbq = [];
  window.fbq = function () {
    var a = Array.prototype.slice.call(arguments);
    window.__fbq.push(a);
    send('fbq', a);
  };
  // Runs last (bubble phase on window), so it sees what attribution.js did to the click.
  window.__hold = false;
  function seen(e) {
    var n = e.target, a = null;
    while (n && n.nodeType === 1) { if (n.nodeName.toLowerCase() === 'a') { a = n; break; } n = n.parentNode; }
    send('click', { type: e.type, defaultPrevented: e.defaultPrevented, button: e.button,
                    ctrl: e.ctrlKey, meta: e.metaKey, shift: e.shiftKey, alt: e.altKey,
                    href: a ? a.getAttribute('href') : null });
    if (window.__hold) e.preventDefault();   // keeps test clicks from opening tabs or leaving the page
  }
  window.addEventListener('click', seen, false);
  window.addEventListener('auxclick', seen, false);
})();
"""


def age_seconds(rec):
    """How far seen_at is from now, in seconds (None if it is not a proper timestamp)."""
    try:
        t = datetime.strptime(rec["seen_at"], "%Y-%m-%dT%H:%M:%S.%fZ").replace(tzinfo=timezone.utc)
        return abs((datetime.now(timezone.utc) - t).total_seconds())
    except Exception:   # noqa: BLE001
        return None


def iso(dt):
    return dt.astimezone(timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")


def is_app_root(href):
    u = urlsplit(href)
    return u.scheme == "https" and u.netloc == "app.keptsoftware.com.au" and u.path in ("", "/")


class Results:
    def __init__(self, echo=True):
        self.rows = []          # (case, name, ok, detail)
        self.echo = echo

    def section(self, n, title):
        if self.echo:
            print("\n== %s. %s" % (n, title), flush=True)

    def check(self, case, name, ok, detail=""):
        ok = bool(ok)
        self.rows.append((case, name, ok, detail))
        if self.echo:
            line = "%s  [%s] %s" % ("PASS" if ok else "FAIL", case, name)
            if not ok and detail:
                line += "\n        -> %s" % (detail,)
            print(line, flush=True)

    @property
    def failed(self):
        return [r for r in self.rows if not r[2]]

    def failing_cases(self):
        seen = []
        for r in self.failed:
            if r[0] not in seen:
                seen.append(r[0])
        return seen


class Server(http.server.ThreadingHTTPServer):
    daemon_threads = True

    def handle_error(self, request, client_address):   # a page navigating away mid-request is normal
        pass


def start_server():
    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def end_headers(self):
            self.send_header("Cache-Control", "no-store")
            super().end_headers()

    srv = Server(("127.0.0.1", 0), functools.partial(Handler, directory=str(SITE)))
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv, "http://127.0.0.1:%d" % srv.server_address[1]


class Env:
    """The browser plus what is different about this run (a normal run, or a deliberately broken one)."""

    def __init__(self, browser, base, attr_source=None, overrides=None):
        self.browser = browser
        self.base = base
        self.attr_source = attr_source      # text served instead of attribution.js (self-test)
        self.overrides = overrides or {}    # {"/": html} served instead of a site page (self-test)
        self._baseline = {}

    def session(self, **opts):
        return Session(self, **opts)

    def baseline(self, path):
        """The page's links exactly as written in the HTML (attribution.js blocked)."""
        if path not in self._baseline:
            s = self.session(block_attr=True)
            try:
                s.goto(path)
                self._baseline[path] = s.hrefs()
            finally:
                s.close()
        return self._baseline[path]


class Session:
    """One fresh browser context (empty storage, no cookies) with its own recorded history."""

    def __init__(self, env, block_attr=False, init=(), leads="ok", referrer=None, google=None):
        self.env = env
        self.base = env.base
        self.seq = 0
        self.events = []      # (seq, kind, payload) sent from the page: fbq calls, clicks, barriers
        self.app_hits = []    # (seq, url) pages the stub app served: the visitor left for the app
        self.posts = []       # (seq, body) contact-form POSTs
        self.requests = []    # every URL the pages asked for
        self.errors = []      # uncaught page errors
        self.leads = leads    # "ok" or "fail": what the stub /api/leads answers
        self._barrier = 0
        self.ctx = env.browser.new_context(viewport={"width": 1280, "height": 900})
        self.ctx.set_default_timeout(15000)
        self.ctx.expose_binding("__keptSink", self._sink)
        self.ctx.add_init_script(INIT_STUB)
        if referrer is not None:
            self.ctx.add_init_script(
                "Object.defineProperty(document, 'referrer', {get: function () { return %s; }, configurable: true});"
                % json.dumps(referrer))
        if google is not None:
            self.ctx.add_init_script("window.KEPT_GOOGLE = %s;" % json.dumps(google))
        for script in init:
            self.ctx.add_init_script(script)
        self.ctx.on("request", lambda r: self.requests.append(r.url))
        # Later routes win: everything outside is blocked, then the app and special files are answered.
        self.ctx.route("**/*", self._outside)
        self.ctx.route(APP + "/**", self._app)
        self.ctx.route(self.base + "/__blank", lambda r: r.fulfill(
            status=200, content_type="text/html", body="<!doctype html><title>blank</title>"))
        for path, body in env.overrides.items():
            pattern = re.compile(r"^%s%s(\?.*)?$" % (re.escape(self.base), re.escape(path)))
            self.ctx.route(pattern, self._serve_text(body))
        if block_attr:
            self.ctx.route(self.base + "/attribution.js", lambda r: r.abort())
        elif env.attr_source is not None:
            self.ctx.route(self.base + "/attribution.js", lambda r: r.fulfill(
                status=200, content_type="application/javascript", body=env.attr_source))
        self.page = self.ctx.new_page()
        self.page.on("pageerror", lambda e: self.errors.append(str(e)))

    # ---- stubs ----

    def _sink(self, source, kind, data):
        self.seq += 1
        self.events.append((self.seq, kind, json.loads(data)))

    @staticmethod
    def _serve_text(body):
        def handle(route):
            route.fulfill(status=200, content_type="text/html; charset=utf-8", body=body)
        return handle

    def _outside(self, route):
        if route.request.url.startswith(self.base):
            route.continue_()
        else:
            route.abort()

    def _app(self, route):
        req = route.request
        path = urlsplit(req.url).path
        cors = {"Access-Control-Allow-Origin": "*", "Access-Control-Allow-Headers": "content-type",
                "Access-Control-Allow-Methods": "GET, POST, OPTIONS"}
        if path == "/api/leads":
            if req.method == "OPTIONS":
                return route.fulfill(status=204, headers=cors)
            if req.method == "POST":
                self.seq += 1
                try:
                    body = json.loads(req.post_data or "null")
                except ValueError:
                    body = "unparseable"
                self.posts.append((self.seq, body))
                if self.leads == "ok":
                    return route.fulfill(status=200, headers=cors, content_type="application/json", body='{"ok":true}')
                return route.fulfill(status=400, headers=cors, content_type="application/json",
                                     body='{"ok":false,"error":"Please fill in your name and email."}')
            return route.fulfill(status=200, headers=cors, content_type="application/json", body='{"ok":false}')
        if req.is_navigation_request():
            self.seq += 1
            self.app_hits.append((self.seq, req.url))
        route.fulfill(status=200, content_type="text/html", body="<!doctype html><title>app</title><p>app stub</p>")

    # ---- driving the page ----

    def close(self):
        self.ctx.close()

    def goto(self, path):
        self.page.goto(self.base + path, wait_until="load")

    def ready(self, hold=False):
        self.page.wait_for_function("typeof window.KeptAttribution === 'object'", polling=20)
        if hold:
            self.page.evaluate("window.__hold = true")

    def visit(self, path, hold=False):
        self.goto(path)
        self.ready(hold)

    def wait(self, predicate, timeout=10.0):
        """Poll until predicate() is true. Returns whether it became true before the deadline."""
        end = time.monotonic() + timeout
        while True:
            if predicate():
                return True
            if time.monotonic() > end:
                return False
            self.page.wait_for_timeout(20)

    def barrier(self):
        """Returns once every earlier event from the page has reached Python (events arrive in order)."""
        self._barrier += 1
        mark = "barrier-%d" % self._barrier
        self.page.evaluate("m => window.__keptSink('barrier', JSON.stringify(m))", mark)
        return self.wait(lambda: any(k == "barrier" and p == mark for _, k, p in self.events))

    def stored_raw(self):
        return self.page.evaluate("localStorage.getItem('kept_attr')")

    def stored(self):
        raw = self.stored_raw()
        return json.loads(raw) if raw else None

    def seed(self, raw):
        self.goto("/__blank")
        self.page.evaluate("v => localStorage.setItem('kept_attr', v)", raw)

    def get(self):
        return self.page.evaluate("window.KeptAttribution.get()")

    def hrefs(self):
        return self.page.evaluate("Array.from(document.querySelectorAll('a[href]'), a => a.getAttribute('href'))")

    def fbq(self, name=None):
        """Params of fbq('track', name, params) calls so far (name None = every tracked event)."""
        return [p[2] if len(p) > 2 else None for _, k, p in self.events
                if k == "fbq" and p and p[0] == "track" and (name is None or p[1] == name)]

    def fbq_calls(self, name):
        return [(seq, p[2] if len(p) > 2 else None) for seq, k, p in self.events
                if k == "fbq" and p and p[0] == "track" and p[1] == name]

    def clicks(self):
        return [p for _, k, p in self.events if k == "click"]

    def start_free(self, i):
        return self.page.locator('a:has-text("Get started free"):visible').nth(i)

    def click(self, target, expect=1, **kw):
        """Click, then wait until the page has reported the click(s). Returns the click records."""
        loc = self.page.locator(target).first if isinstance(target, str) else target
        before = len(self.clicks())
        loc.click(**kw)
        self.wait(lambda: len(self.clicks()) >= before + expect)
        return self.clicks()[before:]

    def synthetic(self, targets, ctrl=True):
        """Clicks dispatched back to back inside the page (so well inside 500 ms).
        targets = [(css selector, index), ...]. Returns performance.now() just before the first."""
        before = len(self.clicks())
        t0 = self.page.evaluate("""([targets, ctrl]) => {
            const t0 = performance.now();
            for (const [sel, idx] of targets) {
              const a = Array.from(document.querySelectorAll(sel))[idx];
              a.dispatchEvent(new MouseEvent('click', {bubbles: true, cancelable: true, view: window, ctrlKey: ctrl}));
            }
            return t0;
        }""", [targets, ctrl])
        self.wait(lambda: len(self.clicks()) >= before + len(targets))
        return t0

    def wait_for_app(self):
        return self.wait(lambda: self.page.url.startswith(APP + "/"))


def case(n, title):
    def deco(fn):
        fn.case_no, fn.title = n, title
        return fn
    return deco


# ---------------------------------------------------------------------------------------------
# 1. Capture
# ---------------------------------------------------------------------------------------------
@case(1, "capture: the tags in the address are saved in the browser")
def case_capture(env, R):
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        rec = s.stored()
        R.check(1, "stores exactly the five tags given, plus landing and seen_at",
                rec is not None and sorted(rec) == sorted(list(TAGS) + ["landing", "seen_at"]), rec)
        R.check(1, "the tag values are stored as given", rec is not None and all(rec.get(k) == v for k, v in TAGS.items()), rec)
        R.check(1, "landing is the page path", rec is not None and rec.get("landing") == "/", rec)
        age = age_seconds(rec or {})
        R.check(1, "seen_at is a current ISO timestamp", age is not None and age < 300, rec)
        R.check(1, "KeptAttribution.get() returns the same record", s.get() == rec, s.get())
        R.check(1, "no cookies are set", s.page.evaluate("document.cookie") == "")
        R.check(1, "no uncaught page errors", not s.errors, s.errors)
    finally:
        s.close()

    s = env.session()
    try:
        s.visit("/?utm_source=google&utm_medium=cpc&utm_campaign=mow_search&utm_content=ad1&utm_term=mow+near%20me&gclid=Cj0K")
        rec = s.stored() or {}
        R.check(1, "all six tags are read (+ and %20 become spaces, then underscores)",
                {k: rec.get(k) for k in ("utm_source", "utm_medium", "utm_campaign", "utm_content", "utm_term", "gclid")} ==
                {"utm_source": "google", "utm_medium": "cpc", "utm_campaign": "mow_search", "utm_content": "ad1",
                 "utm_term": "mow_near_me", "gclid": "Cj0K"}, rec)
        s.visit("/?utm_source=a&utm_source=b")
        R.check(1, "the first of a repeated tag wins", (s.stored() or {}).get("utm_source") == "a", s.stored())
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 2. Decorating app links
# ---------------------------------------------------------------------------------------------
@case(2, "decorate: links to the app carry the tags (and nothing else changes)")
def case_decorate(env, R):
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        problems, roots, others, with_params = [], 0, 0, 0
        saw_request_link = False
        for path in HOME_PAGES:
            s.visit(path)
            now, base = s.hrefs(), env.baseline(path)
            if len(now) != len(base):
                problems.append("%s: %d links, was %d" % (path, len(now), len(base)))
                continue
            for b, n in zip(base, now):
                if is_app_root(b):
                    roots += 1
                    want = b + ("&" if "?" in b else "?") + SUFFIX
                    if "?" in b:
                        with_params += 1
                    if n != want:
                        problems.append("%s: %s -> %s (wanted %s)" % (path, b, n, want))
                else:
                    others += 1
                    saw_request_link = saw_request_link or b.endswith("/request.html")
                    if n != b:
                        problems.append("%s: %s was changed to %s" % (path, b, n))
        R.check(2, "every app-root link gets the tags + kl, after its own parameters (%d links on %d pages)" % (roots, len(HOME_PAGES)),
                roots >= 40 and not problems, problems[:3])
        R.check(2, "links that already had ?plan= / ?demo=1 / ?industry= keep them (%d links)" % with_params, with_params >= 25 and not problems)
        R.check(2, "the app's /request.html link and every other link is byte-for-byte unchanged (%d links)" % others,
                saw_request_link and others > 50 and not problems)
        # Parameters are never duplicated.
        s.visit("/lawn-care/")
        dup = [h for h in s.hrefs() if is_app_root(h) and any(len(v) != 1 for v in parse_qs(urlsplit(h).query).values())]
        R.check(2, "no parameter appears twice in any link", not dup, dup[:2])

        # A link added later, with its own utm_source and a #fragment, is handled at click time.
        s.visit("/", hold=True)
        s.page.evaluate("""() => {
            const a = document.createElement('a');
            a.id = 'dyn'; a.textContent = 'dyn';
            a.href = 'https://app.keptsoftware.com.au/?utm_source=custom&plan=solo#top';
            a.style.cssText = 'position:fixed;left:0;bottom:0;z-index:99999;background:#fff;padding:8px';
            document.body.appendChild(a);
            const b = document.createElement('a');
            b.id = 'blank'; b.textContent = 'blank'; b.target = '_blank';
            b.href = 'https://app.keptsoftware.com.au/?plan=crew';
            b.style.cssText = 'position:fixed;left:80px;bottom:0;z-index:99999;background:#fff;padding:8px';
            document.body.appendChild(b);
        }""")
        s.click("#dyn", modifiers=["Meta"])
        want = ("https://app.keptsoftware.com.au/?utm_source=custom&plan=solo&utm_medium=paid_social&utm_campaign=lawn_time"
                "&utm_content=reel1&gclid=abc&kl=%2F#top")
        got = s.page.get_attribute("#dyn", "href")
        R.check(2, "a link added after load is decorated when clicked: own utm_source kept, none duplicated, #fragment last", got == want, got)
        s.click("#dyn", modifiers=["Meta"])
        R.check(2, "decorating a second time changes nothing", s.page.get_attribute("#dyn", "href") == want)
        recs = s.click("#blank")
        R.check(2, "a target=_blank link is decorated too and is left to the browser (not held back)",
                recs[0]["defaultPrevented"] is False and "kl=%2F" in (s.page.get_attribute("#blank", "href") or ""), recs)
        R.check(2, "no uncaught page errors", not s.errors, s.errors)
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 3. Nothing to say, nothing changed
# ---------------------------------------------------------------------------------------------
@case(3, "a visitor with no tags: links are byte-for-byte unchanged")
def case_clean_profile(env, R):
    s = env.session()
    try:
        problems = []
        for path in HOME_PAGES:
            s.visit(path)
            if s.hrefs() != env.baseline(path):
                problems.append(path)
        R.check(3, "an empty profile visiting %d pages: every link is exactly as written in the HTML" % len(HOME_PAGES), not problems, problems)
        rec = s.stored() or {}
        R.check(3, "the first visit is remembered as a first touch (landing + seen_at only)",
                sorted(rec) == ["landing", "seen_at"] and rec.get("landing") == "/", rec)
        R.check(3, "...but get() has nothing to send (a bare landing path is not attribution)", s.get() is None, s.get())
        s.visit("/")
        s.click(s.start_free(0))
        reached = s.wait_for_app()
        s.barrier()
        R.check(3, "clicking Get started free then leaves for exactly the original address", reached and s.page.url == APP + "/", s.page.url)
        R.check(3, "no uncaught page errors", not s.errors, s.errors)
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 4. Clicks and Meta events
# ---------------------------------------------------------------------------------------------
@case(4, "clicks: one Meta event per click, and the page still gets to the app")
def case_clicks(env, R):
    # a) plain click on "Get started free"
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        recs = s.click("a.btn-accent")
        reached = s.wait_for_app()
        s.barrier()
        leads = s.fbq_calls("Lead")
        R.check(4, "a plain click fires exactly one Lead", len(leads) == 1, s.fbq())
        R.check(4, "...content_name start_free, plan free, category home",
                leads and leads[0][1] == {"content_name": "start_free", "content_category": "home", "plan": "free"}, leads)
        R.check(4, "...and no ViewContent", not s.fbq("ViewContent"))
        R.check(4, "the click was held back (default prevented) so the beacon can leave", recs[0]["defaultPrevented"] is True, recs)
        R.check(4, "then the page goes to the app, carrying the tags", reached and s.page.url == APP + "/?" + SUFFIX, s.page.url)
        R.check(4, "the Lead was sent before the page left, and the app was requested once",
                leads and len(s.app_hits) == 1 and leads[0][0] < s.app_hits[0][0], (leads, s.app_hits))
    finally:
        s.close()

    # b) demo link
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        s.click("a.btn-line")
        reached = s.wait_for_app()
        s.barrier()
        R.check(4, "the demo link fires ViewContent (demo, home), not Lead",
                s.fbq("ViewContent") == [{"content_name": "demo", "content_category": "home"}] and not s.fbq("Lead"), s.fbq())
        R.check(4, "...and goes to ?demo=1 with the tags", reached and s.page.url == APP + "/?demo=1&" + SUFFIX, s.page.url)
    finally:
        s.close()

    # c) modified clicks report but are never taken over
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS, hold=True)
        for i, mod in enumerate(["Meta", "Shift", "Alt"]):
            recs = s.click(s.start_free(i), modifiers=[mod])
            s.barrier()
            R.check(4, "%s-click fires a Lead and does not prevent the default" % mod,
                    len(s.fbq("Lead")) == i + 1 and recs[0]["defaultPrevented"] is False, (s.fbq("Lead"), recs))
        # (a real Control+click is a right click on macOS and never reaches the page as a click, so it is dispatched)
        s.synthetic([("a[href*='plan=crew']", 0)], ctrl=True)
        s.barrier()
        rec = s.clicks()[-1]
        R.check(4, "Control-click fires a Lead and does not prevent the default",
                len(s.fbq("Lead")) == 4 and rec["ctrl"] is True and rec["defaultPrevented"] is False, (s.fbq("Lead"), rec))
        R.check(4, "the page stayed put", s.page.url.startswith(s.base + "/") and not s.app_hits, s.page.url)
        recs = s.click(s.start_free(4), button="middle")
        s.barrier()
        R.check(4, "a middle click counts and is left to the browser",
                len(s.fbq("Lead")) == 5 and recs[0]["type"] == "auxclick" and recs[0]["defaultPrevented"] is False, (len(s.fbq("Lead")), recs))
        s.click(s.start_free(5), button="right", expect=0)
        s.barrier()
        R.check(4, "a right click does not count", len(s.fbq("Lead")) == 5, s.fbq("Lead"))
        s.click("a[href='/privacy']", modifiers=["Meta"])
        s.barrier()
        R.check(4, "a link that is not an app-root link fires nothing", len(s.fbq("Lead")) == 5 and not s.fbq("ViewContent"), s.fbq())
    finally:
        s.close()

    # d) double click
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        s.page.locator("a.btn-accent").first.dblclick()
        reached = s.wait_for_app()
        s.barrier()
        R.check(4, "a double click within 500 ms fires one Lead and makes one trip to the app",
                reached and len(s.fbq("Lead")) == 1 and len(s.app_hits) == 1, (s.fbq(), s.app_hits))
    finally:
        s.close()

    # e) the 500 ms window ends
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS, hold=True)
        t0 = s.synthetic([("a.btn-accent", 0)] * 2)
        s.barrier()
        R.check(4, "two clicks on the same link back to back: one Lead", len(s.fbq("Lead")) == 1, s.fbq("Lead"))
        s.page.wait_for_function("t0 => performance.now() - t0 > 600", arg=t0, polling=20)
        s.synthetic([("a.btn-accent", 0)])
        s.barrier()
        R.check(4, "a click on it more than 500 ms later counts again", len(s.fbq("Lead")) == 2, s.fbq("Lead"))
        s.synthetic([("a.btn-accent", 0), ("a.btn-line", 0)])
        s.barrier()
        R.check(4, "a different link straight after the first is counted, not swallowed by the 500 ms rule",
                len(s.fbq("ViewContent")) == 1 and len(s.fbq("Lead")) == 2, s.fbq())
    finally:
        s.close()

    # f) keyboard
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        before = len(s.clicks())
        s.page.locator("a.btn-accent").first.focus()
        s.page.keyboard.press("Enter")
        s.wait(lambda: len(s.clicks()) > before)
        reached = s.wait_for_app()
        s.barrier()
        R.check(4, "pressing Enter on the link counts once and still reaches the app",
                reached and len(s.fbq("Lead")) == 1 and s.page.url == APP + "/?" + SUFFIX, (s.fbq(), s.page.url))
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 5. Plans
# ---------------------------------------------------------------------------------------------
@case(5, "pricing buttons: the plan travels with the event and the link")
def case_plans(env, R):
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS, hold=True)
        for plan in ("solo", "crew", "team"):
            s.click('a:has-text("Start with %s")' % plan.capitalize(), modifiers=["Meta"])
        s.barrier()
        got = s.fbq("Lead")
        R.check(5, "Start with Solo / Crew / Team: Lead with plan solo, crew, team",
                [g.get("plan") for g in got] == ["solo", "crew", "team"] and all(g.get("content_name") == "start_free" for g in got), got)
    finally:
        s.close()
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        s.click('a:has-text("Start with Solo")')
        reached = s.wait_for_app()
        R.check(5, "a plain click on Start with Solo reaches the app with ?plan=solo and the tags",
                reached and s.page.url == APP + "/?plan=solo&" + SUFFIX, s.page.url)
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 6. Cleaning and the storage rules
# ---------------------------------------------------------------------------------------------
def _seed_visit(s, raw, path="/"):
    s.seed(raw)
    s.visit(path)
    return s.stored_raw()


@case(6, "cleaning, replacing, expiring")
def case_policy(env, R):
    now = datetime.now(timezone.utc)

    # hostile values
    s = env.session()
    try:
        q = ("utm_source=%3Cscript%3Ealert(1)%3C/script%3E%20x"
             "&utm_medium=" + "a" * 300 +
             "&utm_campaign=javascript:alert(1)"
             "&utm_content=%0A%0Dbad%20stuff"
             "&utm_term=%E2%9C%93emoji"
             "&gclid=x%22onmouseover%3D%22alert(1)")
        s.visit("/?" + q)
        rec = s.stored() or {}
        R.check(6, "<script> is stripped, whitespace becomes _ ('scriptalert1/script_x')", rec.get("utm_source") == "scriptalert1/script_x", rec.get("utm_source"))
        R.check(6, "a 300-character value is cut to 100", rec.get("utm_medium") == "a" * 100, len(rec.get("utm_medium", "")))
        R.check(6, "a javascript: string loses its brackets ('javascript:alert1')", rec.get("utm_campaign") == "javascript:alert1", rec.get("utm_campaign"))
        R.check(6, "newlines and spaces become _ ('_bad_stuff')", rec.get("utm_content") == "_bad_stuff", rec.get("utm_content"))
        R.check(6, "emoji are deleted", rec.get("utm_term") == "emoji", rec.get("utm_term"))
        R.check(6, "quotes and = are deleted", rec.get("gclid") == "xonmouseoveralert1", rec.get("gclid"))
        R.check(6, "every stored value uses only the allowed characters and is at most 100 long",
                all(VALUE_OK.match(v) for k, v in rec.items() if k != "seen_at"), rec)
        s.visit("/")
        bad = [h for h in s.hrefs() if is_app_root(h) and re.search(r"[<>\"'\s()]", h)]
        qs = parse_qs(urlsplit(next(h for h in s.hrefs() if is_app_root(h))).query)
        R.check(6, "the links carry the cleaned values, round-tripped intact",
                not bad and qs.get("utm_source") == ["scriptalert1/script_x"] and qs.get("utm_campaign") == ["javascript:alert1"], qs)
        s.visit("/?utm_campaign=" + "b" * 5000 + "&utm_source=%E0%A4%A")
        rec = s.stored() or {}
        R.check(6, "a 5000-character value and a broken %-escape do not break anything",
                rec.get("utm_campaign") == "b" * 100 and rec.get("utm_source") == "%E0%A4%A" and not s.errors, (rec.get("utm_source"), s.errors))
    finally:
        s.close()

    # empty/garbage tags never wipe a good record
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        before = s.stored_raw()
        s.visit("/?utm_source=%3C%3E&utm_term=&gclid=%3C%3E")
        R.check(6, "tags that clean down to nothing do not replace a paid-click record", s.stored_raw() == before, s.stored_raw())
        # later visit with no tags
        s.visit("/vs-jobber.html")
        R.check(6, "a later visit with no tags leaves the paid-click record alone (byte for byte)", s.stored_raw() == before, s.stored_raw())
        # later visit with new tags
        s.visit("/lawn-care/?utm_source=google&utm_medium=cpc&gclid=zzz")
        rec = s.stored() or {}
        R.check(6, "a later visit with new tags replaces it entirely (old tags gone, new landing)",
                rec.get("utm_source") == "google" and rec.get("gclid") == "zzz" and "utm_content" not in rec
                and "utm_campaign" not in rec and rec.get("landing") == "/lawn-care/", rec)
    finally:
        s.close()

    # expiry
    s = env.session()
    try:
        old = json.dumps({"utm_source": "old", "utm_medium": "cpc", "landing": "/old", "seen_at": iso(now - timedelta(days=31))})
        rec = json.loads(_seed_visit(s, old) or "null") or {}
        R.check(6, "a record older than 30 days is replaced by first-touch data",
                "utm_source" not in rec and rec.get("landing") == "/" and (age_seconds(rec) or 1e9) < 300, rec)
        R.check(6, "...and its tags are no longer put on links", s.hrefs() == env.baseline("/"))
        fresh = json.dumps({"utm_source": "keep", "utm_medium": "cpc", "landing": "/x", "seen_at": iso(now - timedelta(days=29))})
        R.check(6, "a record 29 days old is kept as it is", _seed_visit(s, fresh) == fresh)
        R.check(6, "...and still used", (s.get() or {}).get("utm_source") == "keep", s.get())
        future = json.dumps({"utm_source": "future", "landing": "/x", "seen_at": iso(now + timedelta(days=10))})
        rec = json.loads(_seed_visit(s, future) or "null") or {}
        R.check(6, "a record dated in the future is not trusted", "utm_source" not in rec, rec)
    finally:
        s.close()

    # broken storage content
    s = env.session()
    try:
        bad_kinds = ["{not json", '"text"', "null", "[1,2]", '{"utm_source":"x"}',
                     '{"utm_source":"x","seen_at":"not a date"}', '{"utm_source":"x","seen_at":12345}']
        failures = []
        for raw in bad_kinds:
            rec = json.loads(_seed_visit(s, raw) or "null") or {}
            if "utm_source" in rec or rec.get("landing") != "/" or "seen_at" not in rec:
                failures.append(raw)
        R.check(6, "unparseable or unusable stored content is replaced (%d kinds)" % len(bad_kinds), not failures, failures)
        tampered = json.dumps({"utm_source": "<b>x</b>", "evil": "1", "gclid": "a b", "seen_at": iso(now)})
        s.seed(tampered)
        s.visit("/vs-jobber.html")
        got = s.get() or {}
        link = next(h for h in s.hrefs() if is_app_root(h))
        R.check(6, "a fresh record with dirty values is cleaned when read (extra keys dropped)",
                got.get("utm_source") == "bx/b" and got.get("gclid") == "a_b" and "evil" not in got, got)
        R.check(6, "...so links only ever carry the cleaned values", "utm_source=bx%2Fb" in link and "evil" not in link and "%3C" not in link, link)
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 7. Trade pages
# ---------------------------------------------------------------------------------------------
@case(7, "the trade comes from the page")
def case_trades(env, R):
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        for path, trade in (("/lawn-care/", "lawn_care"), ("/wash/", "pressure_washing"), ("/clean/", "cleaning"),
                            ("/handyman/", "handyman"), ("/", "home"), ("/vs-jobber.html", "home")):
            s.visit(path, hold=True)
            n = len(s.fbq("Lead"))
            s.click(s.start_free(0), modifiers=["Meta"])
            s.barrier()
            got = s.fbq("Lead")[n:]
            R.check(7, "%s -> Lead content_category %s" % (path, trade),
                    len(got) == 1 and got[0].get("content_category") == trade and got[0].get("content_name") == "start_free", got)
        s.visit("/lawn-care/", hold=True)
        n = len(s.fbq("Lead"))
        s.click('a[href*="plan=solo"]', modifiers=["Meta"])
        s.barrier()
        got = s.fbq("Lead")[n:]
        R.check(7, "a plan button on a trade page: plan solo, category lawn_care", got and got[0].get("plan") == "solo" and got[0].get("content_category") == "lawn_care", got)
        s.visit("/card/", hold=True)
        s.click("a[href*='demo=1']", modifiers=["Meta"])
        s.barrier()
        R.check(7, "/card/ demo link -> ViewContent category card", s.fbq("ViewContent")[-1:] == [{"content_name": "demo", "content_category": "card"}], s.fbq("ViewContent"))
        s.visit("/lawn-care/")
        link = next(h for h in s.hrefs() if "plan=free&industry=lawn_care" in h)
        R.check(7, "plan=free&industry=lawn_care keeps both and gains the tags", link == APP + "/?plan=free&industry=lawn_care&" + SUFFIX, link)
        R.check(7, "no uncaught page errors", not s.errors, s.errors)
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 8. Contact form
# ---------------------------------------------------------------------------------------------
def _submit_form(s):
    s.page.fill("#leadName", "Test Person")
    s.page.fill("#leadEmail", "test@example.com")
    s.page.click("#leadSubmit")


@case(8, "contact form: sends the attribution, reports the lead, works without the script")
def case_form(env, R):
    s = env.session()
    try:
        s.visit("/?" + TAGS_QS)
        rec = s.stored()
        _submit_form(s)
        s.page.wait_for_selector("#leadStatus.ok")
        s.wait(lambda: s.posts)
        s.barrier()
        body = s.posts[0][1] if s.posts else {}
        R.check(8, "the POST body carries the form fields", body.get("name") == "Test Person" and body.get("email") == "test@example.com", body)
        R.check(8, "...and `attribution` equal to the stored record", body.get("attribution") == rec, body.get("attribution"))
        leads = s.fbq_calls("Lead")
        R.check(8, "a Lead (lead_form, category home) fires once, after the successful response",
                len(leads) == 1 and leads[0][1] == {"content_name": "lead_form", "content_category": "home"} and leads[0][0] > s.posts[0][0], leads)
    finally:
        s.close()

    s = env.session()
    try:
        s.visit("/")
        _submit_form(s)
        s.page.wait_for_selector("#leadStatus.ok")
        s.barrier()
        body = s.posts[0][1] if s.posts else {}
        R.check(8, "a visitor with no tags: no `attribution` in the POST", "attribution" not in body and body.get("email"), body)
        R.check(8, "...and the lead is still reported", len(s.fbq("Lead")) == 1)
    finally:
        s.close()

    s = env.session(leads="fail")
    try:
        s.visit("/?" + TAGS_QS)
        _submit_form(s)
        s.page.wait_for_selector("#leadStatus.err")
        s.barrier()
        R.check(8, "when the server says no, nothing is reported to Meta", not s.fbq("Lead") and len(s.posts) == 1, s.fbq())
    finally:
        s.close()

    s = env.session(block_attr=True)
    try:
        s.goto("/?" + TAGS_QS)
        _submit_form(s)
        s.page.wait_for_selector("#leadStatus.ok")
        s.barrier()
        body = s.posts[0][1] if s.posts else {}
        R.check(8, "with attribution.js blocked the form still posts and succeeds",
                len(s.posts) == 1 and body.get("email") == "test@example.com" and "attribution" not in body, body)
        R.check(8, "...with no page errors and no Meta events", not s.errors and not s.fbq("Lead"), (s.errors, s.fbq()))
        R.check(8, "...and the page's links are the plain ones", s.hrefs() == env.baseline("/"))
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 9. Google (off by default)
# ---------------------------------------------------------------------------------------------
@case(9, "Google: nothing unless the page switches it on")
def case_google(env, R):
    def google_requests(s):
        return [u for u in s.requests if "googletagmanager" in u or "google-analytics" in u or "googleadservices" in u]

    s = env.session()
    try:
        s.visit("/?" + TAGS_QS, hold=True)
        s.click(s.start_free(0), modifiers=["Meta"])
        s.barrier()
        R.check(9, "default: no request to Google at all", not google_requests(s), google_requests(s))
        R.check(9, "default: no gtag and no dataLayer exist, even after a Start free click",
                s.page.evaluate("typeof window.gtag") == "undefined" and s.page.evaluate("typeof window.dataLayer") == "undefined")
        R.check(9, "...while the Meta Lead still fires", len(s.fbq("Lead")) == 1)
    finally:
        s.close()

    for cfg, why in (({"adsId": "", "label": "abc"}, "empty adsId"), ({}, "empty object")):
        s = env.session(google=cfg)
        try:
            s.visit("/?" + TAGS_QS, hold=True)
            s.click(s.start_free(0), modifiers=["Meta"])
            s.barrier()
            R.check(9, "KEPT_GOOGLE with %s: nothing loads or runs" % why,
                    not google_requests(s) and s.page.evaluate("typeof window.gtag") == "undefined", google_requests(s))
        finally:
            s.close()

    s = env.session(google={"adsId": "AW-123", "label": "abc"})
    try:
        s.visit("/?" + TAGS_QS, hold=True)
        dl = "Array.from(window.dataLayer || [], x => Array.from(x, v => v instanceof Date ? 'DATE' : v))"
        R.check(9, "adsId set: gtag.js is requested", [u for u in s.requests if u == "https://www.googletagmanager.com/gtag/js?id=AW-123"] != [], google_requests(s))
        R.check(9, "...gtag exists and the page queued js + config", s.page.evaluate("typeof window.gtag") == "function"
                and s.page.evaluate(dl) == [["js", "DATE"], ["config", "AW-123"]], s.page.evaluate(dl))
        s.click(s.start_free(0), modifiers=["Meta"])
        s.barrier()
        conv = [e for e in s.page.evaluate(dl) if e[:2] == ["event", "conversion"]]
        R.check(9, "a Start free click queues one conversion (send_to AW-123/abc) on the same click as the Lead",
                conv == [["event", "conversion", {"send_to": "AW-123/abc"}]] and len(s.fbq("Lead")) == 1, conv)
        s.synthetic([("a.btn-accent", 0)] * 3)
        s.barrier()
        n_conv = len([e for e in s.page.evaluate(dl) if e[:2] == ["event", "conversion"]])
        R.check(9, "repeated clicks inside 500 ms add one conversion in total, not three", n_conv == 2 and len(s.fbq("Lead")) == 2, n_conv)
        s.click("a.btn-line", modifiers=["Meta"])
        s.barrier()
        R.check(9, "the demo link queues no conversion",
                len([e for e in s.page.evaluate(dl) if e[:2] == ["event", "conversion"]]) == 2 and len(s.fbq("ViewContent")) == 1)
        R.check(9, "no uncaught page errors", not s.errors, s.errors)
    finally:
        s.close()

    s = env.session(google={"adsId": "AW-123", "label": ""})
    try:
        s.visit("/?" + TAGS_QS, hold=True)
        s.click(s.start_free(0), modifiers=["Meta"])
        s.barrier()
        R.check(9, "adsId without a label: the tag loads but no (broken) conversion is sent",
                not [e for e in s.page.evaluate("Array.from(window.dataLayer, x => Array.from(x))") if e[:2] == ["event", "conversion"]])
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 10. Storage that throws
# ---------------------------------------------------------------------------------------------
@case(10, "storage that throws must never break the page")
def case_storage_throws(env, R):
    variants = (
        ("getItem/setItem throw", "Storage.prototype.getItem = function () { throw new Error('blocked'); };"
                                  "Storage.prototype.setItem = function () { throw new Error('blocked'); };"),
        ("window.localStorage throws SecurityError", "Object.defineProperty(window, 'localStorage', {configurable: true,"
                                                     " get: function () { throw new DOMException('denied', 'SecurityError'); }});"),
    )
    for name, script in variants:
        s = env.session(init=[script])
        try:
            s.visit("/?" + TAGS_QS)
            R.check(10, "[%s] the page loads, the script runs, no errors" % name, not s.errors, s.errors)
            links = [h for h in s.hrefs() if is_app_root(h)]
            R.check(10, "[%s] this page view's tags are still put on the links (kept in memory)" % name,
                    links and all(h.endswith(SUFFIX) for h in links), links[:1])
            R.check(10, "[%s] get() still works" % name, (s.get() or {}).get("utm_source") == "facebook", s.get())
            s.click("a.btn-accent")
            reached = s.wait_for_app()
            s.barrier()
            R.check(10, "[%s] clicking Get started free still gets to the app, with one Lead" % name,
                    reached and s.page.url == APP + "/?" + SUFFIX and len(s.fbq("Lead")) == 1, (s.page.url, s.fbq()))
            s.visit("/")
            R.check(10, "[%s] a visit with no tags leaves every link unchanged and get() empty" % name,
                    s.hrefs() == env.baseline("/") and s.get() is None, s.get())
            _submit_form(s)
            s.page.wait_for_selector("#leadStatus.ok")
            R.check(10, "[%s] the contact form still works" % name, len(s.posts) == 1 and "attribution" not in s.posts[0][1], s.posts)
            R.check(10, "[%s] still no uncaught errors" % name, not s.errors, s.errors)
        finally:
            s.close()


# ---------------------------------------------------------------------------------------------
# 11. Referrer
# ---------------------------------------------------------------------------------------------
@case(11, "referrer: only another site counts")
def case_referrer(env, R):
    s = env.session(referrer="https://l.facebook.com/l.php?u=abc")
    try:
        s.visit("/?" + TAGS_QS)
        rec = s.stored() or {}
        R.check(11, "with tags: ref is the referrer's hostname only", rec.get("ref") == "l.facebook.com", rec)
        s.visit("/")
        link = next(h for h in s.hrefs() if is_app_root(h))
        R.check(11, "...and kr travels on the links", link == APP + "/?" + TAGS_QS + "&kl=%2F&kr=l.facebook.com", link)
    finally:
        s.close()

    s = env.session(referrer="https://www.google.com/search?q=lawn+software")
    try:
        s.visit("/lawn-care/")
        rec = s.stored() or {}
        R.check(11, "no tags, outside referrer: stored as a first touch (ref, landing, seen_at)",
                sorted(rec) == ["landing", "ref", "seen_at"] and rec.get("ref") == "www.google.com" and rec.get("landing") == "/lawn-care/", rec)
        links = [h for h in s.hrefs() if is_app_root(h)]
        R.check(11, "...links gain kl and kr only, after their own parameters",
                links and all(h.endswith("&kl=%2Flawn-care%2F&kr=www.google.com") or h.endswith("?kl=%2Flawn-care%2F&kr=www.google.com") for h in links), links[:2])
        R.check(11, "...and get() reports it", (s.get() or {}).get("ref") == "www.google.com", s.get())
    finally:
        s.close()

    for ref, why in ((env.base + "/lawn-care/", "same host (the site linking to itself)"),
                     ("android-app://com.google.android.gm/", "a non-web referrer"), ("", "no referrer")):
        s = env.session(referrer=ref)
        try:
            s.visit("/?" + TAGS_QS)
            R.check(11, "%s: no ref is stored" % why, "ref" not in (s.stored() or {"ref": 1}), s.stored())
        finally:
            s.close()

    s = env.session(referrer="https://WWW.Example.COM:8443/path?x=1")
    try:
        s.visit("/?" + TAGS_QS)
        R.check(11, "the host is lower-cased and the port, path and query are dropped", (s.stored() or {}).get("ref") == "www.example.com", s.stored())
    finally:
        s.close()


# ---------------------------------------------------------------------------------------------
# 12. The pages themselves
# ---------------------------------------------------------------------------------------------
SENTENCE = ("When you sign up or leave your details, we save which link or ad brought you here (the campaign tags in the web "
            "address, the website you came from and the page you landed on) so we know which advertising works. We keep this in our own database and do not send it to anyone.")
TAG = '<script src="/attribution.js" defer></script>'


def site_pages():
    out = []
    for p in sorted(SITE.rglob("*.html")):
        rel = p.relative_to(SITE)
        if rel.parts[0] in (".git", "tools", "node_modules"):
            continue
        out.append(rel)
    return out


def page_url(rel):
    parts = list(rel.parts)
    if parts[-1] == "index.html":
        parts = parts[:-1]
        return "/" + "/".join(parts) + ("/" if parts else "")
    return "/" + "/".join(parts)


@case(12, "pages: the script is on every page that carries the pixel, and nothing Google is in the HTML")
def case_pages(env, R):
    pixel, wrong = [], []
    for rel in site_pages():
        text = (SITE / rel).read_text(encoding="utf-8")
        if "fbq('init'" in text:
            pixel.append(rel)
            right_place = re.search(r"<!-- End Meta Pixel Code -->\s*" + re.escape(TAG), text) is not None
            if text.count(TAG) != 1 or not right_place:
                wrong.append(str(rel))
        elif "attribution.js" in text:
            wrong.append(str(rel) + " (has the script but not the pixel)")
    R.check(12, "%d pages carry the pixel; each has the script tag exactly once, right after the pixel block" % len(pixel),
            len(pixel) >= 15 and not wrong, wrong)
    google = [str(rel) for rel in site_pages()
              if re.search(r"googletagmanager|gtag\(|google-analytics|googleadservices|\bAW-\d", (SITE / rel).read_text(encoding="utf-8"))]
    R.check(12, "no Google tag or Google Ads id anywhere in the HTML", not google, google)
    privacy = (SITE / "privacy.html").read_text(encoding="utf-8")
    R.check(12, "privacy.html has the new sentence, once, in a paragraph of its own",
            privacy.count(SENTENCE) == 1 and ("<p>" + SENTENCE + "</p>") in privacy)
    R.check(12, "privacy.html does not mention Google tags", not re.search(r"Google tag|gtag|Google Ads", privacy))

    s = env.session()
    try:
        failed = []
        for rel in pixel:
            path = page_url(rel)
            try:
                s.visit(path)
            except Exception as e:   # noqa: BLE001
                failed.append("%s (%s)" % (path, type(e).__name__))
        R.check(12, "each of those pages loads attribution.js (window.KeptAttribution exists)", not failed, failed)
        R.check(12, "no uncaught page errors on any page", not s.errors, s.errors)
        R.check(12, "no request to Facebook or Google was even attempted (the pixel is stubbed, Google is off)",
                not [u for u in s.requests if "facebook" in u or "googletagmanager" in u], [u for u in s.requests if "facebook" in u or "google" in u][:3])
    finally:
        s.close()


CASES = [case_capture, case_decorate, case_clean_profile, case_clicks, case_plans, case_policy,
         case_trades, case_form, case_google, case_storage_throws, case_referrer, case_pages]


def run_suite(env, R, only=None):
    for fn in CASES:
        if only and fn.case_no not in only:
            continue
        R.section(fn.case_no, fn.title)
        try:
            fn(env, R)
        except Exception as e:   # noqa: BLE001  a crash is a failure, not a reason to stop
            R.check(fn.case_no, "case crashed: %s" % fn.title, False, "%s: %s" % (type(e).__name__, str(e).splitlines()[0] if str(e) else ""))
    return R


# ---------------------------------------------------------------------------------------------
# Self-test: break things on purpose and make sure the suite notices
# ---------------------------------------------------------------------------------------------
# (id, what is broken, file, text to find (must occur exactly once), replacement)
MUTANTS = [
    ("allow-angle-brackets", "values may contain < and >", "attribution.js",
     r"/[^A-Za-z0-9_.~+%:\/-]/g", r"/[^A-Za-z0-9_.~+%:\/<>-]/g"),
    ("decorate-request-html", "links to /request.html get decorated too", "attribution.js",
     "a.pathname === '/'", "(a.pathname === '/' || a.pathname === '/request.html')"),
    ("lead-twice", "every Start free click fires Lead twice", "attribution.js",
     "      meta('Lead', { content_name: 'start_free', content_category: tradeOf(window.location.pathname), plan: plan });\n",
     "      meta('Lead', { content_name: 'start_free', content_category: tradeOf(window.location.pathname), plan: plan });\n"
     "      meta('Lead', { content_name: 'start_free', content_category: tradeOf(window.location.pathname), plan: plan });\n"),
    ("never-expire", "stored tags never expire", "attribution.js",
     "if (age > MAX_AGE_MS || age < -DAY_MS) return null;", "if (false) return null;"),
    ("duplicate-params", "existing parameters are not respected (keys get duplicated)", "attribution.js",
     "if (val && !(key in have)) add.push(", "if (val) add.push("),
    ("overwrite-on-plain-visit", "a visit with no tags overwrites the paid-click record", "attribution.js",
     "if (!paid && stored()) return;", "if (false) return;"),
    ("hijack-modified-clicks", "ctrl/cmd/shift/alt-clicks are taken over like plain clicks", "attribution.js",
     "e.button === 0 && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey &&", "e.button === 0 &&"),
    ("google-always-on", "Google loads even with the default empty config", "attribution.js",
     "if (!adsId) return;", "if (false) return;"),
    ("demo-fires-lead", "the demo link fires Lead instead of ViewContent", "attribution.js",
     "if (q.demo === '1') viewDemo(); else startFree(", "if (false) viewDemo(); else startFree("),
    ("direct-visits-decorated", "a visit with no tags and no referrer still gets kl on every link", "attribution.js",
     "if (!rec) return false;\n      if (rec.ref) return true;", "return !!rec;\n      if (rec.ref) return true;"),
    ("form-drops-attribution", "the contact form stops sending `attribution`", "index.html",
     "if (attr) data.attribution = attr;", ""),
]


def apply_mutant(m):
    mid, desc, fname, old, new = m
    src = (SITE / fname).read_text(encoding="utf-8")
    if src.count(old) != 1:
        raise SystemExit("self-test error: mutation %r does not apply (the text it replaces occurs %d times in %s)"
                         % (mid, src.count(old), fname))
    return fname, src.replace(old, new)


def selftest(browser, base):
    print("Self-test: the normal suite must pass, then each deliberately broken copy must make it fail.\n", flush=True)
    R = Results(echo=False)
    run_suite(Env(browser, base), R)
    if R.failed:
        print("The unbroken suite already fails (%s); fix that first." % ", ".join(str(c) for c in R.failing_cases()))
        for case_no, name, ok, detail in R.failed:
            print("   FAIL [%s] %s -> %s" % (case_no, name, detail))
        return 1
    print("baseline: %d checks, all pass\n" % len(R.rows), flush=True)
    slipped = []
    for m in MUTANTS:
        fname, text = apply_mutant(m)
        if fname == "attribution.js":
            env = Env(browser, base, attr_source=text)
        else:
            env = Env(browser, base, overrides={"/": text, "/index.html": text})
        R = Results(echo=False)
        run_suite(env, R, only=[c.case_no for c in CASES if c.case_no != 12])
        caught = R.failing_cases()
        names = ["[%s] %s" % (r[0], r[1]) for r in R.failed][:2]
        print("%-26s %s" % (m[0], "CAUGHT by case %s" % ", ".join(str(c) for c in caught) if caught else "NOT CAUGHT  <-- the suite cannot see this"), flush=True)
        print("%-26s   (%s)" % ("", m[1]), flush=True)
        for n in names:
            print("%-26s   e.g. %s" % ("", n[:150]), flush=True)
        if not caught:
            slipped.append(m[0])
    print()
    if slipped:
        print("SELFTEST FAILED: %d of %d broken copies slipped through: %s" % (len(slipped), len(MUTANTS), ", ".join(slipped)))
        return 1
    print("SELFTEST OK: the suite failed for all %d deliberately broken copies" % len(MUTANTS))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--selftest", action="store_true", help="break attribution.js on purpose and check the suite fails")
    ap.add_argument("--only", help="comma-separated case numbers to run, e.g. 4,6")
    ap.add_argument("--browser", choices=["chromium", "webkit"], default="chromium",
                    help="engine to test in (webkit = what Safari and the Facebook/Instagram in-app browsers on iPhone use)")
    args = ap.parse_args()
    only = [int(x) for x in args.only.split(",")] if args.only else None

    started = time.monotonic()
    srv, base = start_server()
    code = 1
    with sync_playwright() as p:
        browser = getattr(p, args.browser).launch()
        try:
            if args.selftest:
                code = selftest(browser, base)
            else:
                R = Results()
                run_suite(Env(browser, base), R, only)
                passed = len(R.rows) - len(R.failed)
                print("\n%s: %d passed, %d failed (%d checks, %.0f s)" % ("PASS" if not R.failed else "FAIL", passed, len(R.failed), len(R.rows), time.monotonic() - started))
                if R.failed:
                    print("failing cases: %s" % ", ".join(str(c) for c in R.failing_cases()))
                code = 0 if not R.failed else 1
        finally:
            browser.close()
            srv.shutdown()
    return code


if __name__ == "__main__":
    sys.exit(main())
