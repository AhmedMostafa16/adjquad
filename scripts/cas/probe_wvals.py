"""Probe W-coefficient valuation deficits across exact-QQ kernel bases.

For each requested weight w: exact rational nullspace of D|V_w (SymPy;
pilot/small weights only), W-expand every basis element by triangular
descent (F = sum_j H_j W^j with H_m = [a0^m]F, W = a0 + rho), and record
m (W-degree), lam_q = min_j(vq(H_j) - 4*j), lam_p = min_j(vp(H_j) - 2*j)
(zero H_j skipped: vpq(0) is not a valuation).

Calibration (hard fail on mismatch): H reproduces m=2, H_2 =
11025*p^4*q^4, H_1 = 0, lam_q = -4, lam_p = 0 (check_s6.py parts C/D);
F0 gives m=1 with zero deficits. Control prediction: all deficits zero
for w <= 14 (no a0^2 room for hidden directions there).

Status: exploratory instrument only. Output is finite-range evidence
(category 2) plus conjectural patterns (category 4); no theorem depends
on it. Cost gate: caller passes small weights first; abort a weight
exceeding --timeout seconds.

Run: python3 scripts/cas/probe_wvals.py --weights 6,8,10
"""

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import Matrix, Poly, binomial, expand

from check_s6 import (F0, H, J1, J2, a0, a1, a2, a3, a4, a5, c, mono_w,
                      rho, vpq)
from emit_witnesses import dmat_int

AVARS = (a0, a1, a2, a3, a4, a5)


def wexpand(F):
    """Return [H_0, ..., H_m] with F = sum H_j W^j, W = a0 + rho."""
    F = expand(F)
    pa0 = Poly(F, a0)
    if pa0 is None or F == 0:
        return []
    m = pa0.degree()
    if m is None:
        return []
    C = {k: expand(pa0.nth(k)) for k in range(m + 1)}
    Hs = [None] * (m + 1)
    for k in range(m, -1, -1):
        acc = C[k]
        for j in range(k + 1, m + 1):
            if Hs[j] != 0:
                acc = acc - binomial(j, k) * Hs[j] * rho ** (j - k)
        Hs[k] = expand(acc)
    return Hs


def deficits(F):
    """Return (m, lam_q, lam_p) for nonzero F; None for F == 0."""
    if expand(F) == 0:
        return None
    Hs = wexpand(F)
    m = len(Hs) - 1
    lam_q, lam_p = None, None
    for j, Hj in enumerate(Hs):
        if expand(Hj) == 0:
            continue
        vq, vp = vpq(Hj)
        dq, dp = vq - 4 * j, vp - 2 * j
        lam_q = dq if lam_q is None else min(lam_q, dq)
        lam_p = dp if lam_p is None else min(lam_p, dp)
    return (m, lam_q if lam_q is not None else 0,
            lam_p if lam_p is not None else 0)


def kernel_basis(w):
    dom, M = dmat_int(w)
    ns = Matrix(M).nullspace()
    basis = []
    for v in ns:
        F = sum(v[i] * (a0 ** dom[i][0]) * (a1 ** dom[i][1]) *
                (a2 ** dom[i][2]) * (a3 ** dom[i][3]) * (a4 ** dom[i][4]) *
                (a5 ** dom[i][5]) for i in range(len(dom)))
        basis.append(expand(F))
    return dom, basis


def calibrate():
    d = deficits(H)
    assert d[0] == 2, "H W-degree %r != 2" % (d,)
    Hs = wexpand(H)
    assert expand(Hs[2] - 11025 * a4 ** 4 * a5 ** 4) == 0, "H_2 mismatch"
    assert expand(Hs[1]) == 0, "H_1 != 0"
    assert (d[1], d[2]) == (-4, 0), "H deficits %r != (-4, 0)" % (d,)
    f = deficits(F0)
    assert f[0] == 1 and (f[1], f[2]) == (0, 0), "F0 deficits %r" % (f,)
    print("calibration OK: H -> (m=2, lam_q=-4, lam_p=0); F0 -> zeros")


def probe(w, timeout):
    t0 = time.time()
    dom, basis = kernel_basis(w)
    t_ns = time.time() - t0
    if t_ns > timeout:
        print("w=%d ABORT nullspace %.1fs > %ds" % (w, t_ns, timeout))
        return None
    recs = []
    for F in basis:
        r = deficits(F)
        if r is not None:
            recs.append(r)
    min_q = min(r[1] for r in recs)
    min_p = min(r[2] for r in recs)
    max_m = max(r[0] for r in recs)
    print("w=%d n=%d dimker=%d maxWdeg=%d minLamQ=%d minLamP=%d nsTime=%.1fs" %
          (w, len(dom), len(recs), max_m, min_q, min_p, t_ns))
    for r in sorted(set(recs)):
        print("    (m=%d, lam_q=%d, lam_p=%d) x%d" %
              (r[0], r[1], r[2], recs.count(r)))
    return recs


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", default="6,8,10")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--skip-calibration", action="store_true")
    args = ap.parse_args(argv)
    if not args.skip_calibration:
        calibrate()
    for s in args.weights.split(","):
        if s.strip() == "":
            continue
        if probe(int(s), args.timeout) is None:
            break
    print("probe_wvals done")


if __name__ == "__main__":
    main()
