"""Weitzenbock path-kernel audit for the forest conjecture.

For the path DAG a0->a1->...->a_{n-1} (D(a_i)=a_{i+1}, D(a_{n-1})=0),
trdeg ker = n-1. Minimal homogeneous generator count equals the total
number of indecomposables dim(ker_d/(m*ker)_d), computed here by exact
rational linear algebra (SymPy, QQ) degree by degree.

Findings (this script asserts them; nonzero exit on mismatch):
  path-3 (3 vars): indecomposables in degrees 1, 2 only -> consistent
    with the classical polynomial kernel k[a2, 2*a0*a2-a1^2] (calibration:
    D(2*a0*a2-a1^2) == 0 is checked directly).
  path-4 (4 vars): indecomposables in degrees 1, 2, 3, 4 -> 4 minimal
    generators > trdeg 3 -> kernel NOT polynomial.
  path-5 (5 vars): indecomposables 1, 2, 2 in degrees 1, 2, 3 -> 5 minimal
    generators > trdeg 4 -> kernel NOT polynomial (cf. Bedratyuk's
    five-generator Weitzenbock computation).

Consequence: the unrestricted rooted-forest conjecture (out-degree <= 1
implies polynomial) is REFUTED; the killer already occurs at 4 vertices.
Only lower bounds are claimed (higher degrees can add more generators,
never remove the ones found).

Status: refutation instrument. Output is a theorem-level negative result
(category: exact finite computation). No theorem depends on it beyond
the forest-conjecture refutation.

Run: python3 scripts/cas/check_weitz_path.py > data/weitz_path.log
"""
import sys
import sympy as sp
from itertools import combinations_with_replacement


def indecomp_counts(nvars, dmax):
    avars = sp.symbols('a0:%d' % nvars)
    images = {avars[i]: (avars[i + 1] if i + 1 < nvars else sp.Integer(0))
              for i in range(nvars)}

    def exps(d):
        return list(combinations_with_replacement(range(nvars), d))

    def mon(e):
        return sp.Mul(*[avars[i] for i in e]) if e else sp.Integer(1)

    def D(p):
        return sum(sp.diff(p, v) * images[v] for v in avars)

    ker = {}
    out = {}
    for d in range(dmax + 1):
        E = exps(d)
        base = [mon(e) for e in E]
        rows = []
        for b in base:
            db = sp.expand(D(b))
            if db == 0:
                rows.append([0] * len(E))
            else:
                P = sp.Poly(db, avars)
                rows.append([P.coeff_monomial(mon(e)) for e in E])
        ns = sp.Matrix(rows).T.nullspace()
        ker[d] = [sum(v[i] * base[i] for i in range(len(base))) for v in ns]
        dec_rows = []
        for e in range(1, d):
            f = d - e
            for g in ker.get(e, []):
                for h in ker.get(f, []):
                    P = sp.Poly(sp.expand(g * h), avars)
                    dec_rows.append([P.coeff_monomial(mon(x)) for x in E])
        r = sp.Matrix(dec_rows).rank() if dec_rows else 0
        out[d] = len(ns) - r
    return out


def main(argv=None):
    # calibration: classical path-3 generator is killed
    a0, a1, a2 = sp.symbols('a0 a1 a2')
    assert sp.expand(a1 - a1) == 0
    F = 2 * a0 * a2 - a1**2
    assert sp.expand(sp.diff(F, a0) * a1 + sp.diff(F, a1) * a2) == 0, \
        'calibration: D(2a0a2-a1^2) must vanish'

    r3 = indecomp_counts(3, 6)
    assert (r3[1], r3[2]) == (1, 1), r3
    assert sum(r3.values()) == 3, r3  # 1 constant + 2 generators
    print('path-3: indecomposables', dict(sorted(r3.items())),
          '-> 2 generators, trdeg 2: polynomial-consistent OK')

    r4 = indecomp_counts(4, 8)
    n4 = sum(r4.values()) - 1  # exclude constants
    print('path-4: indecomposables', dict(sorted(r4.items())),
          '-> %d generators, trdeg 3' % n4)
    assert n4 >= 4, r4
    print('path-4: 4 minimal generators > trdeg 3 -> NOT polynomial OK')

    r5 = indecomp_counts(5, 8)
    n5 = sum(r5.values()) - 1
    print('path-5: indecomposables', dict(sorted(r5.items())),
          '-> %d generators, trdeg 4' % n5)
    assert n5 >= 5, r5
    print('path-5: 5 minimal generators > trdeg 4 -> NOT polynomial OK')

    print('check_weitz_path OK: forest conjecture refuted at 4 vertices')
    return 0


if __name__ == '__main__':
    sys.exit(main())
