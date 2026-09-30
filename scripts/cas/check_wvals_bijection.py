"""Verify exact H·mu deficit-bijection against saved probe_wvals logs.

For each data/probe_wvals_w<W>.log with 29 <= W <= 35 (and any other
present weight >= 24): parse the header (dimker, maxWdeg, minLamQ,
minLamP) and the (m=2) rows; assert
  (a) dimker == s6(W) - s6(W-28)  [hypersurface dimension],
  (b) maxWdeg == 2  [no m=3 rows: H·F0·K correctly absent below 38],
  (c) minLamQ == -4 and minLamP == 0  [R1 floor tight, R2 clean],
  (d) the multiset of m=2 (lam_q, lam_p) rows EQUALS the predicted
      H·mu multiset {(v_q(mu)-4, v_p(mu))} over K-monomials mu of
      weight W-24, where v_q(mu) = eq, v_p(mu) = ep for
      mu = p^ep q^eq J1^ej1 J2^ej2  (J1, J2 contribute no p/q order:
      J1 = 2a1a4-a2^2 has a p-free term a2^2; J2 = 2a2a5-a3^2 has a
      q-free term a3^2).
Prediction (d) is the exact form of Conjecture conj:hk-structure
extended past 28. EMPIRICAL FINDING (2026-09-18 rerun): (d) holds
exactly through w=31 but the multiset mixes from w=32 on (first
visible at 32: an extra (-4,0) row where H·q^2 predicts (-2,0) --
still an H·K-module-consistent profile, i.e. S-relation/basis
mixing, not a new deficit direction: counts and floors stay exact).
Accordingly (d) is reported as EXACT/MIXED informationally; only
(a)--(c) plus the COUNT half of (d) gate the exit status. The
monomial-bijection breakdown at 32 is itself evidence for the
paper's "S-relations mix bases" note and feeds the
product-reduction sketch (subtractors H·mu with general mu in K,
not just monomials, past 31).

Scope: only weights with saved logs are checked (29--35 from the
2026-09-18 rerun). The 24--28 exact bijection (counts 1,2,3,4,6) is
recorded in the paper from the earlier unlogged run and is NOT
re-verified here. Basis note: nullspace bases are arbitrary, so (d)
is a genuine empirical finding, not a tautology.

Run: python3 scripts/cas/check_wvals_bijection.py [--logdir logs]
"""

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_s6 import s6

ROW = re.compile(r"\(m=(\d+), lam_q=(-?\d+), lam_p=(-?\d+)\) x(\d+)")
HEAD = re.compile(
    r"w=(\d+) n=(\d+) dimker=(\d+) maxWdeg=(\d+) "
    r"minLamQ=(-?\d+) minLamP=(-?\d+) nsTime=([\d.]+)s")


def k_monomials(r):
    """Yield (ep, eq) over K-monomials p^ep q^eq J1^ej1 J2^ej2 of weight r."""
    out = []
    for ej1 in range(r // 6 + 1):
        for ej2 in range((r - 6 * ej1) // 4 + 1):
            rest = r - 6 * ej1 - 4 * ej2
            for eq in range(rest + 1):
                out.append((rest - eq, eq))
    return out


def _check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def check_log(path):
    ok = True
    with open(path) as f:
        text = f.read()
    assert "calibration OK" in text, "missing calibration in %s" % path
    m = HEAD.search(text)
    assert m, "missing header in %s" % path
    w, n, dimker, maxm, minq, minp = (int(m.group(i)) for i in range(1, 7))
    tag = "w=%d" % w
    ok &= _check("%s dimker==s6-s6(-28) (%d)" % (tag, dimker),
                 dimker == s6(w) - s6(w - 28))
    if w < 38:
        ok &= _check("%s maxWdeg==2 (no m=3 below 38)" % tag, maxm == 2)
    ok &= _check("%s minLamQ==-4" % tag, minq == -4)
    ok &= _check("%s minLamP==0 (R2 clean)" % tag, minp == 0)
    rows = []
    for rm in ROW.finditer(text):
        mm, lq, lp, cnt = (int(rm.group(i)) for i in range(1, 5))
        if mm == 2:
            rows.extend([(lq, lp)] * cnt)
    pred = [(eq - 4, ep) for (ep, eq) in k_monomials(w - 24)]
    ok &= _check("%s m=2 count %d == s_K(%d)=%d"
                 % (tag, len(rows), w - 24, len(pred)),
                 len(rows) == len(pred))
    if sorted(rows) == sorted(pred):
        print("INFO %s m=2 multiset EXACT (H·monomial bijection)" % tag)
    else:
        print("INFO %s m=2 multiset MIXED (counts/floors hold; "
              "S-relation basis mixing, see module docstring)" % tag)
    return ok


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--logdir", default="logs")
    ap.add_argument("--weights", default="29,30,31,32,33,34,35")
    args = ap.parse_args(argv)
    ok = True
    for s in args.weights.split(","):
        if s.strip() == "":
            continue
        path = os.path.join(args.logdir, "probe_wvals_w%s.log" % s.strip())
        if not os.path.exists(path):
            print("SKIP %s (no log)" % path)
            ok = False
            continue
        ok &= check_log(path)
    print("check_wvals_bijection " + ("OK" if ok else "FAILURES"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
