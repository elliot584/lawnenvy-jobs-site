#!/usr/bin/env python3
"""Checks the short tagged links in vercel.json (keptsoftware.com.au/fb, /yt, /go/lawn ...).

    python3 tools/test-redirects.py             run the checks
    python3 tools/test-redirects.py --selftest  also break the file seven ways and confirm every break is caught

A short link only has to do one thing: send the visitor to a real page with campaign tags that attribution.js and the app will keep. So each one is checked for:
  - a plain lowercase source that does not shadow a real page or folder of the site;
  - a destination that is a real page;
  - utm_source, utm_medium and utm_campaign present, once each, only campaign tags (the app's list), and every value unchanged by the app's cleaning rule
    (so what is saved is exactly what was written here);
  - not permanent (a 308 is cached by browsers for good; a short link may need to point elsewhere one day).
The four older redirects (/clean/privacy ...) must still be there, untouched, and sources must be unique.
"""
import copy, json, pathlib, re, sys
from urllib.parse import parse_qsl, urlsplit

SITE = pathlib.Path(__file__).resolve().parent.parent
TAGS = {"utm_source", "utm_medium", "utm_campaign", "utm_content", "utm_term", "gclid"}
OLD = [("/clean/privacy", "/privacy"), ("/clean/terms", "/terms"), ("/wash/privacy", "/privacy"), ("/wash/terms", "/terms")]


def clean(v):
    """The cleaning rule shared by attribution.js, the app and the database."""
    return re.sub(r"[^A-Za-z0-9_.~+%:/-]", "", re.sub(r"\s+", "_", v))[:100]


def page_exists(path):
    p = path.strip("/")
    return (SITE / "index.html").exists() if not p else any((SITE / c).is_file() for c in (p + ".html", p + "/index.html"))


def check(cfg):
    problems, seen = [], set()
    redirects = cfg.get("redirects", [])
    olds = [(r.get("source"), r.get("destination")) for r in redirects[:len(OLD)]]
    if olds != OLD:
        problems.append("the four older redirects have changed: %r" % olds)
    for r in redirects[len(OLD):]:
        src, dest = r.get("source", ""), r.get("destination", "")
        where = "%s -> %s" % (src, dest)
        if src in seen:
            problems.append("%s: source listed twice" % src)
        seen.add(src)
        if not re.fullmatch(r"/[a-z]+(/[a-z]+)?", src):
            problems.append("%s: the source should be plain lowercase letters, one or two levels" % where)
        first = src.strip("/").split("/")[0]
        if (SITE / (first + ".html")).exists() or ((SITE / first).is_dir() and first not in ("fb", "go")) or (SITE / first / "index.html").exists():
            problems.append("%s: this would hide a real page or folder of the site" % where)
        if r.get("permanent") is not False:
            problems.append("%s: must say \"permanent\": false" % where)
        u = urlsplit(dest)
        if u.scheme or u.netloc or not u.path.startswith("/"):
            problems.append("%s: the destination must be a path on this site" % where)
        elif not page_exists(u.path):
            problems.append("%s: no such page %s" % (where, u.path))
        pairs = parse_qsl(u.query, keep_blank_values=True)
        keys = [k for k, _ in pairs]
        if len(keys) != len(set(keys)):
            problems.append("%s: a tag appears twice" % where)
        for k, v in pairs:
            if k not in TAGS:
                problems.append("%s: %r is not a campaign tag the app keeps" % (where, k))
            if not v or clean(v) != v:
                problems.append("%s: the value %r for %s would be changed (or dropped) by the app's cleaning rule" % (where, v, k))
        for need in ("utm_source", "utm_medium", "utm_campaign"):
            if need not in keys:
                problems.append("%s: no %s" % (where, need))
    return problems, len(redirects) - len(OLD)


def main():
    cfg = json.loads((SITE / "vercel.json").read_text(encoding="utf-8"))
    problems, n = check(cfg)
    for p in problems:
        print("FAIL  " + p)
    if problems or n < 1:
        print("FAIL: %d problem(s) in %d short links" % (len(problems), n))
        sys.exit(1)
    print("PASS: %d short links, each to a real page with clean campaign tags; the four older redirects are untouched" % n)
    if "--selftest" not in sys.argv:
        return
    breaks = {
        "an old redirect changed": lambda c: c["redirects"][0].update(destination="/terms"),
        "a source shadows a real page": lambda c: c["redirects"][4].update(source="/card"),
        "a destination that does not exist": lambda c: c["redirects"][4].update(destination="/nope?utm_source=a&utm_medium=b&utm_campaign=c"),
        "a tag the app would not keep": lambda c: c["redirects"][4].update(destination="/?utm_source=a&utm_medium=b&utm_campaign=c&ref=x"),
        "a value the cleaner would change": lambda c: c["redirects"][4].update(destination="/?utm_source=a b&utm_medium=b&utm_campaign=c"),
        "no campaign": lambda c: c["redirects"][4].update(destination="/?utm_source=a&utm_medium=b"),
        "a permanent short link": lambda c: c["redirects"][4].update(permanent=True),
    }
    missed = []
    for name, fn in breaks.items():
        broken = copy.deepcopy(cfg)
        fn(broken)
        found, _ = check(broken)
        print("%-36s %s" % (name, "CAUGHT" if found else "NOT CAUGHT"))
        if not found:
            missed.append(name)
    if missed:
        print("SELFTEST FAILED: not caught: " + ", ".join(missed))
        sys.exit(1)
    print("SELFTEST OK: all %d deliberate breaks were caught" % len(breaks))


if __name__ == "__main__":
    main()
