"""Exact anchor: a0-degrees, tops, valuations of F0, H, F46.
Slot map: slot0 = a0 (wt 8); slots 4,5 = p,q (wt 1).
F0/H copied verbatim from scripts/cas/check_hf0.sage; F46 parsed from
data/witness_w46.txt with the scripts/cas/check_f46hf0.sage parser.
Run: python3 scripts/cas/check_tops.py (stdout -> data/tops.log)
"""
from fractions import Fraction

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


def top_a0(P):
    m = max(e[0] for e in P)
    return m, {e[1:]: c for e, c in P.items() if e[0] == m}


ok = True


def check(name, P, exp_deg, exp_top, exp_vp, exp_vq):
    global ok
    m, T = top_a0(P)
    vp = min(e[3] for e in T)
    vq = min(e[4] for e in T)
    good = (m == exp_deg and T == exp_top and vp == exp_vp and vq == exp_vq)
    ok = ok and good
    print('%s: deg_a0=%d top=%s vp=%d vq=%d %s'
          % (name, m, T, vp, vq, 'OK' if good else 'MISMATCH'), flush=True)


check('F0', F0, 1, {(0, 0, 0, 2, 4): Fraction(1)}, 2, 4)
check('H', H, 2, {(0, 0, 0, 4, 4): Fraction(11025)}, 4, 4)
# NOTE: witness file stores the cleared integral F46 (content 1); its top
# coefficient is 121550625 = 18375/4 * 26460 (Phase-4 scalar). Valuations
# and degree are scalar-insensitive, so the cleared value is asserted.
check('F46', F46, 4, {(0, 0, 0, 6, 8): Fraction(121550625)}, 6, 8)
print('ALL OK' if ok else 'FAILURE', flush=True)
raise SystemExit(0 if ok else 1)
