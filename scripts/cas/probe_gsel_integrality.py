"""Probe: do the producer-SELECTED genMonos ever have non-integral coefficients?

For each weight with emitted witness data, compare the producer's selected
genMonos (selIdx) against integrality of their exact-QQ coefficients. A
selected genMono with a non-integral coefficient is a case where the emitted
Gsel (int(c) truncation) disagrees with the true coefficient vector (and with
Lean's coordIn, which takes the numerator).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import Matrix, Rational, Poly, expand  # noqa: E402
from check_s6 import Dmono, mono_w, s6, F0, H, J1, J2, a0, a1, a2, a3, a4, a5  # noqa: E402

GEN_WTS = [1, 1, 6, 4, 14, 24]
GENS = [a4, a5, J1, J2, F0, H]


def gen_mono_exps(w):
    out = []
    for eh in range(w // 24 + 1):
        for ef in range((w - 24 * eh) // 14 + 1):
            for ej2 in range((w - 24 * eh - 14 * ef) // 4 + 1):
                for ej1 in range((w - 24 * eh - 14 * ef - 4 * ej2) // 6 + 1):
                    for ep in range(w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 + 1):
                        rest = w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 - ep
                        out.append((ep, rest, ej1, ej2, ef, eh))
    return out


def main():
    for w in [0, 1, 4, 6, 10, 11, 12, 13, 14]:
        dom = mono_w(w)
        ridx = {m: i for i, m in enumerate(dom)}
        n = len(dom)
        sel = gen_mono_exps(w)
        cols = []
        for exps in sel:
            f = 1
            for g, e in zip(GENS, exps):
                f = f * g ** e
            d = Poly(expand(f), a0, a1, a2, a3, a4, a5).as_dict()
            col = [0] * n
            for (i0, i1, i2, i3, i4, i5), c in d.items():
                if (i0, i1, i2, i3, i4, i5) in ridx:
                    col[ridx[(i0, i1, i2, i3, i4, i5)]] += c
            integral = all(Rational(c).q == 1 for c in d.values())
            cols.append((exps, col, integral))
        Ecols_int = [[int(Rational(x)) for x in c] for _, c, _ in cols]
        Eq = Matrix(Ecols_int).T if Ecols_int else Matrix.zeros(n, 0)
        pivc = Eq.rref()[1] if Ecols_int else ()
        selIdx = sorted(pivc)
        k = len(selIdx)
        nonint = [exps for exps, _, ok in cols if not ok]
        sel_nonint = [sel[i] for i in selIdx if not cols[i][2]]
        print("w=%d: n=%d k=%d s6=%d" % (w, n, k, len(sel)))
        if nonint:
            print("   non-integral genMonos: %s" % nonint)
        if sel_nonint:
            print("   !! SELECTED non-integral: %s" % sel_nonint)
        else:
            print("   selected genMonos all integral: OK")


if __name__ == "__main__":
    main()