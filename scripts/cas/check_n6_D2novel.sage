"""D2-novelty: F22 in k[G,H20] at Fibonacci weight 22?
F22 = a0*M + N (M = a5^4*a6*G4; N 10 terms from check_N6_D2.py).
Columns: G-monomials (Fib weights (1,1,6,4,14)) of weight 22 plus
H20 times weight-2 G-monomials. F0^{(6)} (wt 25), H_B (wt 24) excluded
by weight. Exact QQ rank vs augmented rank (sage sparse).
Verdict False ("not in span") = novelty PROVED.
Run: sage scripts/cas/check_n6_D2novel.sage (stdout log)
"""
from collections import defaultdict


def Q(a, b=1):
    return QQ(a) / b


FIB6 = (13, 8, 5, 3, 2, 1, 1)
GW = (1, 1, 6, 4, 14)
G1 = {(0, 0, 0, 0, 0, 1, 0): Q(1)}
G2 = {(0, 0, 0, 0, 0, 0, 1): Q(1)}
G3 = {(0, 0, 1, 0, 0, 1, 0): Q(2),
      (0, 0, 0, 2, 0, 0, 0): Q(-1)}
G4 = {(0, 0, 0, 1, 0, 0, 1): Q(2),
      (0, 0, 0, 0, 2, 0, 0): Q(-1)}
G5 = {(0, 1, 0, 0, 0, 2, 4): Q(105),
      (0, 0, 1, 1, 1, 1, 3): Q(-105),
      (0, 0, 1, 0, 3, 1, 2): Q(35),
      (0, 0, 0, 2, 3, 0, 2): Q(35),
      (0, 0, 0, 1, 5, 0, 1): Q(-21),
      (0, 0, 0, 0, 7, 0, 0): Q(3)}
GENS = [G1, G2, G3, G4, G5]
H20 = {(0, 0, 0, 4, 4, 0, 0): Q(-19, 480),
       (0, 0, 0, 5, 2, 0, 1): Q(293, 1800),
       (0, 0, 0, 6, 0, 0, 2): Q(-49, 450),
       (0, 0, 1, 2, 4, 1, 0): Q(19, 120),
       (0, 0, 1, 3, 2, 1, 1): Q(-59, 90),
       (0, 0, 1, 4, 0, 1, 2): Q(59, 180),
       (0, 0, 2, 0, 4, 2, 0): Q(-1, 8),
       (0, 0, 2, 1, 2, 2, 1): Q(1, 2),
       (0, 1, 0, 0, 5, 2, 0): Q(-1, 15),
       (0, 1, 0, 1, 3, 2, 1): Q(1, 3),
       (0, 1, 1, 0, 1, 3, 2): Q(-1, 1),
       (1, 0, 0, 0, 0, 4, 3): Q(1, 1)}
NTERMS = [((0, 0, 6, 2, 0, 0), Q(-1, 72)),
          ((0, 0, 7, 0, 0, 1), Q(5, 756)),
          ((0, 1, 4, 2, 1, 0), Q(1, 12)),
          ((0, 1, 5, 0, 1, 1), Q(-1, 54)),
          ((0, 2, 2, 2, 2, 0), Q(-1, 9)),
          ((0, 2, 3, 0, 2, 1), Q(-1, 27)),
          ((1, 0, 2, 3, 2, 0), Q(-1, 9)),
          ((1, 1, 0, 3, 3, 0), Q(2, 9)),
          ((1, 1, 1, 1, 3, 1), Q(1, 3)),
          ((2, 0, 0, 0, 4, 2), Q(-7, 6))]


def pmul(A, B):
    R = defaultdict(QQ)
    for a, ca in A.items():
        for b, cb in B.items():
            k = tuple(x + y for x, y in zip(a, b))
            R[k] += ca * cb
    return {k: v for k, v in R.items() if v != 0}


def ppow(A, n):
    R = {(0,) * 7: QQ(1)}
    for _ in range(n):
        R = pmul(R, A)
    return R


def wt(P):
    return {sum(e[i] * FIB6[i] for i in range(7)) for e in P}


def expand_ge(ge):
    R = {(0,) * 7: QQ(1)}
    for i, e in enumerate(ge):
        if e:
            R = pmul(R, ppow(GENS[i], e))
    return R


def genmons(W):
    out = []

    def rec(i, rem, cur):
        if i == 4:
            if rem % GW[4] == 0:
                out.append(tuple(cur + [rem // GW[4]]))
            return
        for e in range(rem // GW[i] + 1):
            rec(i + 1, rem - e * GW[i], cur + [e])
    rec(0, W, [])
    return out


t = cputime()
M = pmul(pmul(ppow({(0, 0, 0, 0, 0, 1, 0): QQ(1)}, 4),
               {(0, 0, 0, 0, 0, 0, 1): QQ(1)}), G4)
N = {(0,) + e: c for e, c in NTERMS}
F22 = dict(pmul({(1, 0, 0, 0, 0, 0, 0): QQ(1)}, M))
for k, v in N.items():
    F22[k] = F22.get(k, QQ(0)) + v
F22 = {k: v for k, v in F22.items() if v != 0}
assert wt(F22) == {22}, 'F22 weight fault'
print('target terms: %d' % len(F22), flush=True)
cols = []
for ge in genmons(22):
    E = expand_ge(ge)
    assert wt(E) == {22}, 'column weight fault %s' % (ge,)
    cols.append(E)
for ge in [(2, 0, 0, 0, 0), (1, 1, 0, 0, 0), (0, 2, 0, 0, 0)]:
    E = pmul(H20, expand_ge(ge))
    assert wt(E) == {22}, 'H20-column weight fault'
    cols.append(E)
print('ncols: %d' % len(cols), flush=True)
for j, C in enumerate(cols):
    if C == F22:
        print('CONSTRUCTION FAULT: column %d equals target' % j, flush=True)
        raise SystemExit(2)
rows = {}
for C in cols:
    for m in C:
        if m not in rows:
            rows[m] = len(rows)
for m in F22:
    if m not in rows:
        rows[m] = len(rows)
Mmat = Matrix(QQ, len(rows), len(cols), sparse=True)
for j, C in enumerate(cols):
    for m, c in C.items():
        Mmat[rows[m], j] = c
t = cputime()
r1 = Mmat.rank()
Ma = Matrix(QQ, len(rows), len(cols) + 1, sparse=True)
for j, C in enumerate(cols):
    for m, c in C.items():
        Ma[rows[m], j] = c
for m, c in F22.items():
    Ma[rows[m], len(cols)] = c
r2 = Ma.rank()
print('rank = %d aug = %d t=%.1fs' % (r1, r2, cputime() - t), flush=True)
print('F22 in k[G,H20]: %s' % (r1 == r2), flush=True)
