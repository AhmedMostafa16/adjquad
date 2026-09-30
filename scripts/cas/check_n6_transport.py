"""Transported torsion relation: (a5)^2*phi(F46) - E_B == 0 in A6.
phi shifts N=5 6-slots (a0..a5) to N=6 7-slots (0,e0..e5).
E_B = phi(E) with E the seven-term B-expression from
scripts/cas/sing_R.sage:4-5, via q->a6, J1->2a2a5-a3^2, J2->G4, H->H_B.
Also asserts uniform Fibonacci weights (48 both sides).
Run: python3 scripts/cas/check_n6_transport.py (stdout -> data/n6_transport.log)
"""
from fractions import Fraction
from collections import defaultdict

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

FIB6 = (13, 8, 5, 3, 2, 1, 1)


def shift(P):
    return {(0,) + e: c for e, c in P.items()}


def pmul(A, B):
    R = defaultdict(Fraction)
    for a, ca in A.items():
        for b, cb in B.items():
            k = tuple(x + y for x, y in zip(a, b))
            R[k] += ca * cb
    return {k: v for k, v in R.items() if v != 0}


def ppow(A, n):
    R = {(0,) * 7: Fraction(1)}
    for _ in range(n):
        R = pmul(R, A)
    return R


def padd(A, B, s=1):
    R = defaultdict(Fraction, A)
    for k, v in B.items():
        R[k] += s * v
    return {k: v for k, v in R.items() if v != 0}


def wt(P):
    return {sum(e[i] * FIB6[i] for i in range(7)) for e in P}


def evar(i):
    e = [0] * 7
    e[i] = 1
    return {(tuple(e)): Fraction(1)}


A1, A2, A3, A4, A5, A6 = (evar(i) for i in (1, 2, 3, 4, 5, 6))
J1B = padd({(0, 0, 1, 0, 0, 1, 0): Fraction(2)}, ppow(A3, 2), s=-1)
J2B = padd({(0, 0, 0, 1, 0, 0, 1): Fraction(2)}, ppow(A4, 2), s=-1)
HB = shift(H)
PHI46 = shift(F46)
# J1B should be 2a2a5-a3^2; J2B = G4 = 2a3a6-a4^2
E_B = defaultdict(Fraction)
for coeff, mon in [(40000, (6, 7, 0, 0)), (193200, (4, 6, 2, 0)),
                   (325164, (2, 5, 4, 0)), (148225, (0, 4, 6, 0)),
                   (840, (2, 3, 1, 1)), (770, (0, 2, 3, 1)),
                   (1, (0, 0, 0, 2))]:
    qe, j1e, j2e, he = mon
    T = ppow({(0, 0, 0, 0, 0, 0, 1): Fraction(1)}, qe)
    T = pmul(T, ppow(J1B, j1e))
    T = pmul(T, ppow(J2B, j2e))
    T = pmul(T, ppow(HB, he))
    for k, v in T.items():
        E_B[k] += Fraction(coeff) * v
E_B = {k: v for k, v in E_B.items() if v != 0}
LHS = pmul(ppow(A5, 2), PHI46)
REL = padd(LHS, E_B, s=-1)

ok = True


def check(name, cond):
    global ok
    print('%s %s' % ('PASS' if cond else 'FAIL', name), flush=True)
    ok = ok and cond


check('J1B = 2a2a5-a3^2', J1B == {(0, 0, 1, 0, 0, 1, 0): Fraction(2),
                                  (0, 0, 0, 2, 0, 0, 0): Fraction(-1)})
check('J2B = G4 = 2a3a6-a4^2', J2B == {(0, 0, 0, 1, 0, 0, 1): Fraction(2),
                                       (0, 0, 0, 0, 2, 0, 0): Fraction(-1)})
check('E_B uniform weight 48', wt(E_B) == {48})
check('a5^2 phi(F46) uniform weight 48', wt(LHS) == {48})
check('(a5)^2 phi(F46) - E_B == 0', REL == {})
print('E_B terms: %d; LHS terms: %d' % (len(E_B), len(LHS)), flush=True)
print('n6-transport OK' if ok else 'n6-transport FAILED', flush=True)
raise SystemExit(0 if ok else 1)
