#!/usr/bin/env python3
"""Every page that carries the Meta Pixel carries the RIGHT one, the same way.

    python3 tools/test-pixel.py             run the checks
    python3 tools/test-pixel.py --selftest  also break a temp copy six ways and confirm each break is caught

PIXEL_ID is the Pixel ID shown in Meta Events Manager: Datasets, "kept software", Settings (created 27 August 2026). On 24 October 2026 the site was found to have sent
1049765071100614 on every page since 27 August. That number is the ad account's (Events Manager's address bar says act=1049765071100614), not the pixel's, so the pixel was never
the one receiving the site's events. This test exists so that cannot happen again unnoticed. If the pixel ever changes, change PIXEL_ID here and on the pages together.

For every .html page that mentions the pixel (outside tools/):
  - exactly one fbq('init', '<PIXEL_ID>');
  - exactly one <noscript> image whose address is https://www.facebook.com/tr?id=<PIXEL_ID>&ev=PageView&noscript=1;
  - exactly one fbq('track', 'PageView');
  - no other pixel-looking number (13 to 17 digits) in an init or a tr?id= address.
"""
import copy, os, pathlib, re, shutil, subprocess, sys, tempfile

PIXEL_ID = "841447128961693"
ROOT = pathlib.Path(os.environ.get("KEPT_PIXEL_ROOT") or pathlib.Path(__file__).resolve().parent.parent)

INIT = re.compile(r"fbq\(\s*['\"]init['\"]\s*,\s*['\"](\d+)['\"]\s*\)")
TR = re.compile(r"facebook\.com/tr\?id=(\d+)&ev=PageView&noscript=1")
TRACK = re.compile(r"fbq\(\s*['\"]track['\"]\s*,\s*['\"]PageView['\"]\s*\)")
ANY_ID = re.compile(r"(?:init['\"]\s*,\s*['\"]|tr\?id=)(\d{13,17})")


def pages(root):
    for p in sorted(root.rglob("*.html")):
        rel = p.relative_to(root)
        if rel.parts[0] in ("tools", ".git", "node_modules"):
            continue
        yield rel, p.read_text(encoding="utf-8")


def check(root):
    problems, n = [], 0
    for rel, text in pages(root):
        if "fbq(" not in text and "facebook.com/tr" not in text:
            continue
        n += 1
        inits, trs, tracks = INIT.findall(text), TR.findall(text), TRACK.findall(text)
        if inits != [PIXEL_ID]:
            problems.append("%s: fbq init is %r, expected exactly one %s" % (rel, inits, PIXEL_ID))
        if trs != [PIXEL_ID]:
            problems.append("%s: the noscript image is %r, expected exactly one %s" % (rel, trs, PIXEL_ID))
        if len(tracks) != 1:
            problems.append("%s: %d PageView track calls, expected 1" % (rel, len(tracks)))
        stray = sorted(set(ANY_ID.findall(text)) - {PIXEL_ID})
        if stray:
            problems.append("%s: another pixel-looking number: %s" % (rel, ", ".join(stray)))
    return problems, n


def main():
    problems, n = check(ROOT)
    for p in problems:
        print("FAIL  " + p)
    if problems or n < 10:
        print("FAIL: %d problem(s) across %d pages with the pixel%s" % (len(problems), n, " (too few pages found: is the folder right?)" if n < 10 else ""))
        sys.exit(1)
    print("PASS: %d pages carry the pixel, every one with %s in the init and the noscript image, one PageView each" % (n, PIXEL_ID))
    if "--selftest" not in sys.argv:
        return
    breaks = {
        "init uses the ad account number": lambda t: t.replace("fbq('init', '%s')" % PIXEL_ID, "fbq('init', '1049765071100614')", 1),
        "noscript image uses another number": lambda t: t.replace("tr?id=%s&" % PIXEL_ID, "tr?id=1049765071100614&", 1),
        "noscript image missing": lambda t: re.sub(r"<noscript>.*?</noscript>", "", t, count=1, flags=re.S),
        "two inits": lambda t: t.replace("fbq('init', '%s');" % PIXEL_ID, "fbq('init', '%s'); fbq('init', '%s');" % (PIXEL_ID, PIXEL_ID), 1),
        "PageView call removed": lambda t: TRACK.sub("", t, count=1),
        "init one digit out": lambda t: t.replace("fbq('init', '%s')" % PIXEL_ID, "fbq('init', '%s')" % (PIXEL_ID[:-1] + "4"), 1),
    }
    missed = []
    for name, fn in breaks.items():
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="kept-pixel-"))
        try:
            for rel, text in pages(ROOT):
                dest = tmp / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(text, encoding="utf-8")
            victim = tmp / "index.html"
            before = victim.read_text(encoding="utf-8")
            after = fn(before)
            if after == before:
                print("%-38s CANNOT BREAK (the text it expects is not in index.html: update this test)" % name)
                missed.append(name)
                continue
            victim.write_text(after, encoding="utf-8")
            found, _ = check(tmp)
            print("%-38s %s" % (name, "CAUGHT" if found else "NOT CAUGHT"))
            if not found:
                missed.append(name)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    if missed:
        print("SELFTEST FAILED: " + ", ".join(missed))
        sys.exit(1)
    print("SELFTEST OK: all %d deliberate breaks were caught" % len(breaks))


if __name__ == "__main__":
    main()
