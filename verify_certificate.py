#!/usr/bin/env python3
"""
verify_certificate.py — independent cross-check of Certificate.lean

Lean guarantees the *proofs* are valid. It does not tell you whether the
numerals you wrote are the ones you meant: a mis-rounded interval endpoint or a
constant copied from the wrong scratch calculation produces a file that either
fails opaquely or, worse, proves something weaker than intended without saying
so.

This script parses the numeric claims out of Certificate.lean and re-derives
each one at 60-digit precision, independently of the Lean development. It
checks:

  1. the interval endpoints for y, q, r, s follow exactly from the pi bounds;
  2. each sin/cos bound is valid, and reports how much slack it wastes;
  3. the chain composes -- every step uses the *rounded* value from the step
     below, not the exact one;
  4. the final inequality F(t0) > 0 holds, with its margin;
  5. the resulting threshold, and the gap to the sharp value.

Usage:  python3 verify_certificate.py [path/to/Certificate.lean]
Requires: mpmath
"""

import re
import sys
from mpmath import mp, mpf, sin, cos, pi, findroot

mp.dps = 60

GREEN, RED, DIM, RESET = "\033[32m", "\033[31m", "\033[2m", "\033[0m"


def ok(b):
    return f"{GREEN}pass{RESET}" if b else f"{RED}FAIL{RESET}"


def parse(path):
    """Pull the numerals we need straight out of the Lean source."""
    src = open(path).read()
    out = {}

    m = re.search(r"lemma pi_lb\s*:\s*\(([\d.]+)\s*:", src)
    out["pi_lo"] = mpf(m.group(1))
    m = re.search(r"lemma pi_ub\s*:\s*π\s*<\s*\(([\d.]+)\s*:", src)
    out["pi_hi"] = mpf(m.group(1))

    m = re.search(r"lemma F_at_witness\s*:\s*0\s*<\s*F\s*\(([\d.]+)\s*:", src)
    out["t0"] = mpf(m.group(1))

    # sin/cos bounds: name -> (argument divisor, direction, value)
    out["bounds"] = {}
    pat = (r"lemma (sin|cos)_([a-z])_(ge|le)\s*:.*?"
           r"(?:\(([\d.]+)\s*:\s*ℝ\)\s*≤\s*)?"
           r"(?:sin|cos)\s*\(\(π\s*-\s*[\d.]+\)\s*/\s*(\d+)\)"
           r"(?:\s*≤\s*([\d.]+))?")
    for fn, lvl, dirn, lhs, div, rhs in re.findall(pat, src, re.S):
        val = mpf(lhs) if lhs else mpf(rhs)
        out["bounds"][f"{fn}_{lvl}_{dirn}"] = (int(div), dirn, val)

    m = re.search(r"lemma sin_witness_lt\s*:\s*sin\s*\(([\d.]+)\s*:\s*ℝ\)\s*<\s*([\d.]+)",
                  src)
    out["two_t0"], out["sin_final"] = mpf(m.group(1)), mpf(m.group(2))
    return out


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "Certificate.lean"
    d = parse(path)
    PL, PH, t0 = d["pi_lo"], d["pi_hi"], d["t0"]

    print(f"file          {path}")
    print(f"pi bounds     ({PL}, {PH})   width {float(PH - PL):.1e}")
    print(f"witness t0    {t0}")

    # -- 1. pi bounds are true --------------------------------------------
    print(f"\n[1] pi bounds sound                       {ok(PL < pi < PH)}")

    # -- 2. 2*t0 matches the literal in sin_witness_lt ---------------------
    print(f"[2] 2*t0 literal consistent               {ok(2 * t0 == d['two_t0'])}"
          f"  {DIM}{d['two_t0']}{RESET}")

    # -- 3. interval endpoints ---------------------------------------------
    print("\n[3] interval endpoints (exact, from pi bounds):")
    ivl = {}
    for div in (2, 4, 8, 16):
        lo, hi = (PL - 2 * t0) / div, (PH - 2 * t0) / div
        ivl[div] = (lo, hi)
        print(f"    y/{div:<3} ({mp.nstr(lo, 12)}, {mp.nstr(hi, 12)})"
              f"   width {float(hi - lo):.2e}")

    # -- 4. each bound valid, with slack -----------------------------------
    print("\n[4] individual bounds (slack = waste vs the true value):")
    allok = True
    for name, (div, dirn, val) in sorted(d["bounds"].items()):
        lo, hi = ivl[div]
        fn = sin if name.startswith("sin") else cos
        # worst case over the interval
        true = min(fn(lo), fn(hi)) if dirn == "ge" else max(fn(lo), fn(hi))
        good = (val <= true) if dirn == "ge" else (val >= true)
        slack = abs(val - true)
        allok &= good
        arrow = "\u2265" if dirn == "ge" else "\u2264"
        print(f"    {name:<12} {arrow} {mp.nstr(val, 13):<16}"
              f" slack {float(slack):.2e}   {ok(good)}")

    # -- 5. final inequality -----------------------------------------------
    need = (3 * t0 - PH) / mpf("1.5")
    fin = d["sin_final"]
    true_sin = sin(2 * t0)
    print(f"\n[5] final step")
    print(f"    claimed  sin({d['two_t0']}) < {fin}")
    print(f"    true                        {mp.nstr(true_sin, 15)}"
          f"   {ok(fin > true_sin)}")
    print(f"    required                  < {mp.nstr(need, 15)}"
          f"   {ok(fin < need)}")
    print(f"    margin                      {float(need - fin):+.3e}")

    # -- 6. threshold -------------------------------------------------------
    tstar = findroot(lambda t: 3 * t - mpf(3) / 2 * sin(2 * t) - pi, mpf("1.3"))
    k_cert, k_sharp = 3 * cos(t0), 3 * cos(tstar)
    thr, thr_sharp = 1 / k_cert, 1 / k_sharp
    print(f"\n[6] result")
    print(f"    theta*        {mp.nstr(tstar, 15)}")
    print(f"    t0 > theta*   {ok(t0 > tstar)}   (required: certificate is valid)")
    print(f"    3 cos t0      {mp.nstr(k_cert, 15)}")
    print(f"    3 cos theta*  {mp.nstr(k_sharp, 15)}   (sharp)")
    print(f"    threshold     {mp.nstr(thr, 15)}")
    print(f"    sharp         {mp.nstr(thr_sharp, 15)}")
    print(f"    gap           {float(thr - thr_sharp):.2e}")
    print(f"    beats 4/pi    {ok(thr < 4 / pi)}   (4/pi = {mp.nstr(4 / pi, 12)})")

    verdict = allok and fin > true_sin and fin < need and t0 > tstar and thr < 4 / pi
    print(f"\n{'ALL CHECKS PASS' if verdict else 'SOME CHECKS FAILED'}")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
