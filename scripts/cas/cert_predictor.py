"""Cheap per-weight certificate prediction (NO nullspace, seconds at w=24).

For weight w: n = len(mono_w(w)); Ecols = exact-QQ expansions of all
genMono exponent tuples in the mono basis; D0 = lcm of all coefficient
denominators; density = nonzero entries / (n * #cols) of the D0-scaled
Ecols matrix (Gsel is a column subset of Ecols, so this density is
representative of the selected certificate). Coupling note: imports the
private emit_witnesses._gen_mono_exps (enumeration ORDER matters for
downstream certificates); the count pins in test_cert_predictor.py
(55 @14, 213 @24) fail loudly if the producer order changes. This
script proves nothing about spanning; prediction only.

Run: python3 scripts/cas/cert_predictor.py --weights 13,14,15,24
"""

import argparse
import os
import sys
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import Poly, Rational, expand

from check_s6 import F0, H, J1, J2, a0, a1, a2, a3, a4, a5, mono_w
from emit_witnesses import _gen_mono_exps


def predict(w):
    dom = mono_w(w)
    ridx = {m: i for i, m in enumerate(dom)}
    n = len(dom)
    gens = [a4, a5, J1, J2, F0, H]
    sel = _gen_mono_exps(w)
    D0, nnz, total = 1, 0, 0
    hcount = 0
    for exps in sel:
        if exps[5] > 0:
            hcount += 1
        f = 1
        for g, e in zip(gens, exps):
            f *= g ** e
        d = Poly(expand(f), a0, a1, a2, a3, a4, a5).as_dict()
        for c in d.values():
            q = Rational(c).q
            D0 = D0 * q // gcd(D0, q)
        col = [Rational(0)] * n
        for (i0, i1, i2, i3, i4, i5), c in d.items():
            col[ridx[(i0, i1, i2, i3, i4, i5)]] += Rational(c)
        for x in col:
            total += 1
            if int(x * D0) != 0:
                nnz += 1
    return {"w": w, "n": n, "genMonos": len(sel), "Hcount": hcount,
            "D0": D0, "density": nnz / total if total else 1.0}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", default="13,14,15,24")
    args = ap.parse_args(argv)
    for s in args.weights.split(","):
        if s.strip() == "":
            continue
        p = predict(int(s))
        print("w=%(w)d n=%(n)d genMonos=%(genMonos)d Hcount=%(Hcount)d "
              "D0=%(D0)d density=%(density).4f" % p)
    print("cert_predictor OK")


if __name__ == "__main__":
    main()
