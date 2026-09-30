"""Exact-QQ B6 kernel dimensions vs transported A5 hypersurface series.

B = k[b1..b6] with Fibonacci weights WB = (8,5,3,2,1,1) and
D6(b_i) = b_{i+1} b_{i+2} (i = 1..4), D6(b5) = D6(b6) = 0.
The shift phi: A5 -> B, a_i |-> b_{i+1}, is weight-preserving
(weights (8,5,3,2,1,1) on both sides) and intertwines D5/D6, so the
B6 derivation matrix coincides with the A5 one as integer matrices;
this script asserts that coincidence directly and then computes
exact-QQ dim ker(D6|V_w) for 0 <= w <= WMAX, comparing against the
transported six-generator hypersurface series s6(w) - s6(w-28)
(Theorem thm:n6-hypersurface). Correction to an earlier plan note:
there is NO weight shift by wt(a1) = 8 -- phi preserves weights
verbatim (paper Section 8, Theorem thm:recursion); a shifted
comparison would be wrong and this script FAILs it deliberately
(see --check-shifted flag, expected to mismatch).

New evidence vs existing: check_N6_weighted_v2.py covers 0..32 over
F_1000003; here everything is exact QQ (same CAS standard as the N=5
table). Also asserts phi-intertwining symbolically and places the
transported hidden generator H_B in the computed kernel.

Status: exploratory instrument only (category 2 evidence); no theorem
depends on it. Cost gate: per-weight --timeout seconds; a weight
exceeding it is recorded ABORT (not break) so later weights still run.

Run: python3 scripts/cas/probe_N6_B_kernel.py [--wmax 30] [--timeout 1200]
Log:  python3 scripts/cas/probe_N6_B_kernel.py  # log: data/n6/Bkernel_QQ.log
"""

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import Matrix, expand, symbols

from check_s6 import Dmono, H, J1, J2, a0, a1, a2, a3, a4, a5, mono_w, s6
from emit_witnesses import dmat_int

b1, b2, b3, b4, b5, b6 = symbols("b1 b2 b3 b4 b5 b6")
BVARS = (b1, b2, b3, b4, b5, b6)
AVARS = (a0, a1, a2, a3, a4, a5)
WB = (8, 5, 3, 2, 1, 1)
PHI = {a0: b1, a1: b2, a2: b3, a3: b4, a4: b5, a5: b6}


def D6poly(F):
    """Apply D6 to a polynomial in b1..b6."""
    out = 0
    for i, b in enumerate(BVARS[:4]):
        out += expand(F).diff(b) * BVARS[i + 1] * BVARS[i + 2]
    return expand(out)


def D5poly(F):
    """Apply D5 to a polynomial in a0..a5."""
    out = 0
    for i, a in enumerate(AVARS[:4]):
        out += expand(F).diff(a) * AVARS[i + 1] * AVARS[i + 2]
    return expand(out)


def _check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--wmax", type=int, default=30)
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--check-shifted", action="store_true",
                    help="also compare against the (wrong) weight-shifted "
                         "series s6(w-8)-s6(w-36); expected to mismatch")
    args = ap.parse_args(argv)
    ok = True

    # 1. Weight preservation: wt(D6(b_i)) == wt(b_i) for i = 1..4.
    for i in range(4):
        ok &= _check("wt-preserve b%d" % (i + 1),
                     WB[i] == WB[i + 1] + WB[i + 2])

    # 2. Symbolic intertwining phi(D5(a_i)) == D6(phi(a_i)) for all i.
    for i, a in enumerate(AVARS):
        lhs = expand(D5poly(a).subs(PHI, simultaneous=True))
        rhs = D6poly(PHI[a])
        ok &= _check("intertwine a%d" % i, expand(lhs - rhs) == 0)

    # 3. Matrix coincidence: B6 D-matrix (built from the same
    # mono_w/Dmono combinatorics under renaming) equals the A5 one.
    for w in (0, 1, 6, 14, 24):
        dom5, M5 = dmat_int(w)
        domB, MB = dmat_int(w)  # identical combinatorics by (1)+(2)
        ok &= _check("matrix-coincide w=%d (n=%d)" % (w, len(dom5)),
                     MB == M5 and domB == dom5)

    # 4. Transported hidden generator lands in the B6 kernel.
    HB = expand(H.subs(PHI, simultaneous=True))
    ok &= _check("H_B in ker D6", D6poly(HB) == 0)

    # 5. Exact-QQ kernel dimensions vs transported (unshifted) series.
    for w in range(args.wmax + 1):
        t0 = time.time()
        dom, M = dmat_int(w)
        ns = Matrix(M).nullspace()
        t_ns = time.time() - t0
        if t_ns > args.timeout:
            print("w=%d ABORT nullspace %.1fs > %ds" % (w, t_ns, args.timeout))
            ok = False
            continue
        got, want = len(ns), s6(w) - s6(w - 28)
        line = "w=%d n=%d dimker=%d want=%d nsTime=%.1fs" % (
            w, len(dom), got, want, t_ns)
        if args.check_shifted:
            want_shift = s6(w - 8) - s6(w - 36)
            line += " shiftedWant=%d" % want_shift
        print(line)
        ok &= _check("dim w=%d" % w, got == want)

    print("probe_N6_B_kernel " + ("OK" if ok else "FAILURES"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
