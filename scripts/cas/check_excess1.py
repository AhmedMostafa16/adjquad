"""Exact check: eps-1 monomial tops (F46HF0, F0^3F46, F0^2).
Asserts computed (a0-degree, v_p of top, excess) against hand values.
This is a value check, not a membership solve: the claim is a computed
valuation plus closed-form arithmetic, so a rank-vs-augmented solve would
be vacuous theater here. Scalar-insensitive (cleared F46): only degree
and valuations are asserted, never coefficients.
Run: python3 scripts/cas/check_excess1.py (stdout -> data/excess1.log)
"""
from fractions import Fraction
from collections import defaultdict
from math import ceil

F0 = {(1, 0, 0, 0, 2, 4): Fraction(1),
      (0, 1, 1, 1, 1, 3): Fraction(-1),
      (0, 1, 0, 3, 1, 2): Fraction(1, 3),
      (0, 0, 2, 3, 0, 2): Fraction(1, 3),
      (0, 0, 1, 5, 0, 1): Fraction(-1, 5),
      (0, 0, 0, 7, 0, 0): Fraction(1, 35)}
HMONO = [((11025), [2, 0, 0, 0, 4, 4]),
         ((-22050), [1, 1, 1, 1, 3, 3]),
         ((7350), [1, 1, 0, 3, 3, 2]),
         ((7350), [1, 0, 2, 3, 2, 2]),
         ((-4410), [1, 0, 1, 5, 2, 1]),
         ((630), [1, 0, 0, 7, 2, 0]),
         ((11025), [0, 2, 2, 2, 2, 2]),
         ((-7350), [0, 2, 1, 4, 2, 1]),
         ((1225), [0, 2, 0, 6, 2, 0]),
         ((6720), [0, 1, 5, 0, 1, 3]),
         ((-16800), [0, 1, 4, 2, 1, 2]),
         ((9450), [0, 1, 3, 4, 1, 1]),
         ((-1540), [0, 1, 2, 6, 1, 0]),
         ((-2208), [0, 0, 7, 0, 0, 3]),
         ((4368), [0, 0, 6, 2, 0, 2]),
         ((-2352), [0, 0, 5, 4, 0, 1]),
         ((385), [0, 0, 4, 6, 0, 0])]
H = {tuple(e): Fraction(c) for (c, e) in HMONO}
F46 = {}
with open('data/witness_w46.txt') as fh:
    for line in fh:
        sp = line.strip().split()
        F46[tuple(map(int, sp[0].split(',')))] = Fraction(sp[1])


def pmul(A, B):
    R = defaultdict(Fraction)
    for a, ca in A.items():
        for b, cb in B.items():
            k = tuple(x + y for x, y in zip(a, b))
            R[k] += ca * cb
    return {k: v for k, v in R.items() if v != 0}


ok = True


def check(name, P, exp_m, exp_vp, exp_eps):
    global ok
    m = max(e[0] for e in P)
    T = [e[1:] for e in P if e[0] == m]
    vp = min(e[3] for e in T)
    eps = vp - ceil(3 * m / 2)
    good = (m == exp_m and vp == exp_vp and eps == exp_eps)
    ok = ok and good
    print('%s: m=%d vp(top)=%d eps=%d nterms=%d %s'
          % (name, m, vp, eps, len(P), 'OK' if good else 'MISMATCH'),
          flush=True)


check('F46HF0', pmul(pmul(F46, H), F0), 7, 12, 1)
check('F0^3F46', pmul(pmul(pmul(F0, F0), F0), F46), 7, 12, 1)
check('F0^2', pmul(F0, F0), 2, 4, 1)
print('ALL OK' if ok else 'FAILURE', flush=True)
raise SystemExit(0 if ok else 1)
