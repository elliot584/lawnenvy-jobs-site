/*
 * Kept - attribution.js
 *
 * Loaded on every page that carries the Meta Pixel. It does three things:
 *
 *  1. Remembers which ad or link brought the visitor: the campaign tags in the web
 *     address (utm_source, utm_medium, utm_campaign, utm_content, utm_term, gclid),
 *     the referring site's hostname and the landing path. Kept in this browser only
 *     (localStorage key "kept_attr") and dropped after 30 days.
 *  2. Adds those tags to links that go to the app (https://app.keptsoftware.com.au/),
 *     because the site and the app are different hostnames and cannot share storage.
 *     The app reads utm_*, gclid, kl (landing path) and kr (referrer host).
 *  3. Tells Meta when someone clicks "Start free" (Lead) or the demo (ViewContent).
 *     Google conversion tracking is built in but OFF until a page sets
 *     window.KEPT_GOOGLE = { adsId: 'AW-...', label: '...' } before this script runs.
 *
 * Plain browser JS, no dependencies. Nothing in here may ever break a page, so every
 * entry point is wrapped in try/catch.
 */
(function () {
  'use strict';
  try {
    start();
  } catch (e) { /* never break the page */ }

  function start() {
    var GOOGLE = (window.KEPT_GOOGLE) || { adsId: '', label: '' };
    if (window.KeptAttribution) return;   // loaded twice: do nothing the second time

    var KEY = 'kept_attr';
    var APP_HOST = 'app.keptsoftware.com.au';
    var DAY_MS = 24 * 60 * 60 * 1000;
    var MAX_AGE_MS = 30 * DAY_MS;     // stored tags older than this are dropped
    var DEDUPE_MS = 500;              // a second click on the same link inside this is ignored
    var NAV_DELAY_MS = 150;           // lets Meta's beacon leave before the page does
    var TAGS = ['utm_source', 'utm_medium', 'utm_campaign', 'utm_content', 'utm_term', 'gclid'];
    var LINK_KEYS = TAGS.concat(['kl', 'kr']);   // what is added to app links, in this order
    var TRADES = { 'lawn-care': 'lawn_care', 'wash': 'pressure_washing', 'clean': 'cleaning', 'handyman': 'handyman', 'card': 'card' };

    var fallback = null;              // only used when the browser refuses to store anything
    var lastEl = null, lastAt = 0;    // for ignoring a double click
    var leaving = false;              // true while our own delayed navigation is pending

    function step(fn) { try { fn(); } catch (e) { /* never break the page */ } }

    // ---- values ---------------------------------------------------------------

    // The one cleaning rule for every value (the app and the database use the same):
    // runs of whitespace become "_", anything outside [A-Za-z0-9_.~+%:/-] is deleted,
    // cut to 100 characters. An empty result means "drop the key".
    function clean(v) {
      if (v === null || v === undefined) return '';
      return String(v).replace(/\s+/g, '_').replace(/[^A-Za-z0-9_.~+%:\/-]/g, '').slice(0, 100);
    }

    function decode(s) {
      s = s.replace(/\+/g, ' ');
      try { return decodeURIComponent(s); } catch (e) { return s; }
    }

    // Query string -> object. The first occurrence of a key wins (like URLSearchParams.get).
    function parseQuery(qs) {
      var out = Object.create(null);
      qs = String(qs || '').replace(/^\?/, '');
      if (!qs) return out;
      var parts = qs.split('&');
      for (var i = 0; i < parts.length; i++) {
        if (!parts[i]) continue;
        var eq = parts[i].indexOf('=');
        var k = decode(eq < 0 ? parts[i] : parts[i].slice(0, eq));
        var v = eq < 0 ? '' : decode(parts[i].slice(eq + 1));
        if (!(k in out)) out[k] = v;
      }
      return out;
    }

    function strip(host) { return host.replace(/^www\./, ''); }

    // Hostname of the referring page, only when it is another site.
    function referrerHost() {
      var r = document.referrer;
      if (!r) return '';
      var a = document.createElement('a');
      a.href = r;
      if (a.protocol !== 'http:' && a.protocol !== 'https:') return '';
      var host = (a.hostname || '').toLowerCase();
      if (!host || strip(host) === strip((window.location.hostname || '').toLowerCase())) return '';
      return clean(host);
    }

    function tradeOf(path) {
      var seg = String(path || '').split('/')[1] || '';
      seg = seg.toLowerCase();
      return Object.prototype.hasOwnProperty.call(TRADES, seg) ? TRADES[seg] : 'home';
    }

    // ---- storage --------------------------------------------------------------

    // A stored record, rebuilt from the whitelisted keys only and cleaned again, or null
    // when it is not a usable record (not an object, no readable date, older than 30
    // days, or dated more than a day in the future).
    function usable(o) {
      if (!o || Object.prototype.toString.call(o) !== '[object Object]') return null;
      var t = typeof o.seen_at === 'string' ? Date.parse(o.seen_at) : NaN;
      if (isNaN(t)) return null;
      var age = new Date().getTime() - t;
      if (age > MAX_AGE_MS || age < -DAY_MS) return null;
      var out = {}, i, v;
      for (i = 0; i < TAGS.length; i++) {
        v = clean(o[TAGS[i]]);
        if (v) out[TAGS[i]] = v;
      }
      v = clean(o.ref); if (v) out.ref = v;
      v = clean(o.landing); if (v) out.landing = v;
      out.seen_at = new Date(t).toISOString();
      return out;
    }

    function stored() {
      var raw, o;
      try { raw = window.localStorage.getItem(KEY); } catch (e) { return null; }
      if (!raw) return null;
      try { o = JSON.parse(raw); } catch (e) { return null; }
      return usable(o);
    }

    function save(rec) {
      var ok = false;
      try { window.localStorage.setItem(KEY, JSON.stringify(rec)); ok = true; } catch (e) { /* private mode etc. */ }
      fallback = ok ? null : rec;     // keep it for this page view if it could not be stored
    }

    // Runs once per page load.
    //  - Any campaign tag in the address: replace what is stored (the last paid click wins).
    //  - Otherwise, if nothing usable is stored: store the first touch (referrer + landing).
    //  - Otherwise leave storage alone.
    function remember() {
      var q = parseQuery(window.location.search), rec = {}, paid = false, i, v;
      for (i = 0; i < TAGS.length; i++) {
        v = clean(q[TAGS[i]]);
        if (v) { rec[TAGS[i]] = v; paid = true; }
      }
      if (!paid && stored()) return;
      v = referrerHost(); if (v) rec.ref = v;
      v = clean(window.location.pathname); if (v) rec.landing = v;
      if (!paid && !rec.ref && !rec.landing) return;
      rec.seen_at = new Date().toISOString();
      save(rec);
    }

    function current() { return stored() || fallback; }

    // Only a record that says something about where the visitor came from counts: a
    // campaign tag or an outside referrer. A bare landing path is stored (it marks the
    // first visit) but is never sent anywhere, so a direct visit leaves every link and
    // every form exactly as it was.
    function hasSignal(rec) {
      if (!rec) return false;
      if (rec.ref) return true;
      for (var i = 0; i < TAGS.length; i++) if (rec[TAGS[i]]) return true;
      return false;
    }

    // The cleaned record (tags, ref, landing, seen_at) or null.
    function get() {
      var rec = current();
      if (!hasSignal(rec)) return null;
      var out = {};
      for (var k in rec) if (Object.prototype.hasOwnProperty.call(rec, k)) out[k] = rec[k];
      return out;
    }

    // ---- links to the app ------------------------------------------------------

    function isAppRoot(a) {
      return a.protocol === 'https:' && a.hostname === APP_HOST && a.port === '' && a.pathname === '/';
    }

    // Appends the saved tags (+ kl landing, kr referrer) to an app link. Existing
    // parameters (plan, industry, demo ...) stay as they are and are never duplicated
    // or overwritten. A link with nothing to add is not touched at all.
    function decorate(a, rec) {
      if (!rec || !isAppRoot(a)) return;
      var href = a.getAttribute('href');
      if (!href) return;
      var h = href.indexOf('#');
      var head = h < 0 ? href : href.slice(0, h);
      var tail = h < 0 ? '' : href.slice(h);
      var q = head.indexOf('?');
      var have = parseQuery(q < 0 ? '' : head.slice(q + 1));
      var add = [], i, key, val;
      for (i = 0; i < LINK_KEYS.length; i++) {
        key = LINK_KEYS[i];
        val = key === 'kl' ? rec.landing : key === 'kr' ? rec.ref : rec[key];
        if (val && !(key in have)) add.push(key + '=' + encodeURIComponent(val));
      }
      if (!add.length) return;
      a.setAttribute('href', head + (q < 0 ? '?' : (/[?&]$/.test(head) ? '' : '&')) + add.join('&') + tail);
    }

    function decorateAll() {
      var rec = get();
      if (!rec) return;
      var links = document.querySelectorAll('a[href]');
      for (var i = 0; i < links.length; i++) step(function () { decorate(links[i], rec); });
    }

    function anchorOf(node) {
      while (node && node !== document) {
        if (node.nodeType === 1 && node.nodeName && node.nodeName.toLowerCase() === 'a' && node.hasAttribute('href')) return node;
        node = node.parentNode;
      }
      return null;
    }

    // ---- events ---------------------------------------------------------------

    var adsId = clean(GOOGLE && GOOGLE.adsId);
    var label = clean(GOOGLE && GOOGLE.label);

    function meta(event, params) {
      try { if (typeof window.fbq === 'function') window.fbq('track', event, params); } catch (e) { /* ignore */ }
    }

    // Google Ads conversion, on the same click as the Meta Lead. Does nothing unless the
    // page switched Google on (adsId) and gave the conversion label.
    function googleConversion() {
      try {
        if (adsId && label && typeof window.gtag === 'function') {
          window.gtag('event', 'conversion', { send_to: adsId + '/' + label });
        }
      } catch (e) { /* ignore */ }
    }

    function startFree(plan) {
      meta('Lead', { content_name: 'start_free', content_category: tradeOf(window.location.pathname), plan: plan });
      googleConversion();
    }

    function viewDemo() {
      meta('ViewContent', { content_name: 'demo', content_category: tradeOf(window.location.pathname) });
    }

    // For other conversions on the site, e.g. the contact form: track('lead_form').
    function track(name) {
      var n = clean(name);
      if (n) meta('Lead', { content_name: n, content_category: tradeOf(window.location.pathname) });
    }

    function onClick(e) {
      try {
        var a = anchorOf(e.target);
        if (!a || !isAppRoot(a)) return;
        decorate(a, get());   // again at click time: covers links added later
        var plain = e.type === 'click' && e.button === 0 && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey &&
          !e.defaultPrevented && (!a.target || a.target === '_self') && !a.hasAttribute('download');
        if (leaving) { if (plain) e.preventDefault(); return; }   // our own navigation is on its way
        var now = new Date().getTime();
        if (a === lastEl && now - lastAt < DEDUPE_MS) return;     // a double click counts once
        lastEl = a; lastAt = now;
        var q = parseQuery(a.search);
        if (q.demo === '1') viewDemo(); else startFree(clean(q.plan) || 'free');
        if (plain) {
          // Hold the page for a moment so the Meta beacon can leave, then go on to the
          // link. Any other kind of click (new tab, new window, download ...) just
          // reports and lets the browser do its thing.
          e.preventDefault();
          leaving = true;
          var dest = a.href;
          setTimeout(function () {
            try { window.location.assign(dest); } catch (err) { window.location.href = dest; }
          }, NAV_DELAY_MS);
          setTimeout(function () { leaving = false; }, 3000);   // if the user cancelled or came back
        }
      } catch (err) { /* never break a click */ }
    }

    function refresh(e) {
      try {
        var a = anchorOf(e.target);
        if (a && isAppRoot(a)) decorate(a, get());
      } catch (err) { /* ignore */ }
    }

    // ---- Google (off unless window.KEPT_GOOGLE.adsId is set) ----------------------

    function startGoogle() {
      if (!adsId) return;
      window.dataLayer = window.dataLayer || [];
      if (typeof window.gtag !== 'function') window.gtag = function () { window.dataLayer.push(arguments); };
      window.gtag('js', new Date());
      window.gtag('config', adsId);
      var s = document.createElement('script');
      s.async = true;
      s.src = 'https://www.googletagmanager.com/gtag/js?id=' + encodeURIComponent(adsId);
      (document.head || document.documentElement).appendChild(s);
    }

    // ---- go ---------------------------------------------------------------------

    window.KeptAttribution = {
      get: function () { try { return get(); } catch (e) { return null; } },
      track: function (name) { step(function () { track(name); }); }
    };

    step(remember);
    step(startGoogle);
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', function () { step(decorateAll); });
    } else {
      step(decorateAll);
    }
    document.addEventListener('click', onClick, true);
    document.addEventListener('auxclick', function (e) { if (e.button === 1) onClick(e); }, true);
    document.addEventListener('mousedown', refresh, true);
    document.addEventListener('contextmenu', refresh, true);
    window.addEventListener('pageshow', function (e) { if (e.persisted) leaving = false; });
  }
})();
