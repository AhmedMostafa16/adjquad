"""Discriminant: rank of the four-seed generated subspace at m=14.
G = {mu*d : d in {d1..d4}, mu in K6-monomials of complementary degree}.
All vectors explicit products (no elimination in construction); ONE
rank call. g=94 with extracted-span 93 => extraction missed a dimension.
g<=93 => consistent with M-proj 93 (rank-call camp).
Run: sage scripts/cas/check_n6_m14gen.sage (stdout log)
"""
from collections import defaultdict


def Q(a, b=1):
    return QQ(a) / b


G1 = {(0, 0, 0, 0, 1, 0): Q(1)}
G2 = {(0, 0, 0, 0, 0, 1): Q(1)}
G3 = {(0, 1, 0, 0, 1, 0): Q(2), (0, 0, 2, 0, 0, 0): Q(-1)}
G4 = {(0, 0, 1, 0, 0, 1): Q(2), (0, 0, 0, 2, 0, 0): Q(-1)}
G5 = {(1, 0, 0, 0, 2, 4): Q(105),
      (0, 1, 1, 1, 1, 3): Q(-105),
      (0, 1, 0, 3, 1, 2): Q(35),
      (0, 0, 2, 3, 0, 2): Q(35),
      (0, 0, 1, 5, 0, 1): Q(-21),
      (0, 0, 0, 7, 0, 0): Q(3)}
GENS = [G1, G2, G3, G4, G5]
HBMONO = [((11025), [2, 0, 0, 0, 4, 4]),
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
HB = {tuple(e): Q(c) for (c, e) in HBMONO}
MD1 = {(0, 0, 0, 0, 4, 3): QQ(1)}
MD2 = {(0, 0, 1, 0, 4, 2): QQ(2), (0, 0, 0, 2, 4, 1): QQ(-1)}
M3 = {(0, 0, 0, 4, 2, 1): Q(1),
      (0, 0, 1, 2, 2, 2): Q(-4),
      (0, 0, 2, 0, 2, 3): Q(-16, 21),
      (0, 1, 0, 0, 3, 3): Q(200, 21)}
M8 = {(0, 0, 0, 4, 4, 0): Q(1),
      (0, 0, 1, 2, 4, 1): Q(-4),
      (0, 0, 2, 0, 4, 2): Q(17, 3),
      (0, 1, 0, 0, 5, 2): Q(-10, 3)}
DIRS = [(MD1, 7), (MD2, 7), (M3, 7), (M8, 8)]


def pmul(A, B):
    R = defaultdict(QQ)
    for a, ca in A.items():
        for b, cb in B.items():
            k = tuple(x + y for x, y in zip(a, b))
            R[k] += ca * cb
    return {k: v for k, v in R.items() if v != 0}


def ppow(A, n):
    R = {(0,) * 6: QQ(1)}
    for _ in range(n):
        R = pmul(R, A)
    return R


def expand_ge(ge):
    R = {(0,) * 6: QQ(1)}
    for i, e in enumerate(ge):
        if e:
            R = pmul(R, ppow(GENS[i], e))
    return R


def R_tuples(d):
    out = []
    for t in range(d // 7 + 1):
        r0 = d - 7 * t
        for k in range(r0 // 2 + 1):
            for l in range((r0 - 2 * k) // 2 + 1):
                r = r0 - 2 * k - 2 * l
                for i in range(r + 1):
                    out.append((i, r - i, k, l, t))
    return out


def K6mons(d):
    out = [expand_ge(fe) for fe in R_tuples(d)]
    if d >= 10:
        for fe in R_tuples(d - 10):
            out.append(pmul(HB, expand_ge(fe)))
    return out


t = cputime()
Gvecs = []
for (Md, md) in DIRS:
    for mu in K6mons(14 - md):
        Gvecs.append(pmul(mu, Md))
print('generated vectors: %d' % len(Gvecs), flush=True)
uni = list({mm for G in Gvecs for mm in G})
print('universe: %d' % len(uni), flush=True)
idx = {m: i for i, m in enumerate(uni)}
M = Matrix(QQ, len(uni), len(Gvecs), sparse=True)
for j, G in enumerate(Gvecs):
    for m, c in G.items():
        M[idx[m], j] = c
t = cputime()
r = M.rank()
print('rank(generated) = %d t=%.1fs' % (r, cputime() - t), flush=True)
print('gen DONE', flush=True)
