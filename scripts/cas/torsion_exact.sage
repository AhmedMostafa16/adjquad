"""Exact QQ torsion at headline weights via nullity(M') + Hilbert series.
excess_r(w) = [nullity(M') - (ngB - dimC5(W))] - dimC5(w),
dimC5 exact from the hypersurface series s6(W)-s6(W-28).
M' = C5-span matrix restricted to p^r-free rows (small: <=6k rows).
Run: sage scripts/cas/torsion_exact.sage  (stdout log)
"""
from collections import defaultdict

WT = (8, 5, 3, 2, 1, 1)
GW = (1, 1, 6, 4, 14, 24)
P = {(0, 0, 0, 0, 1, 0): 1}
Q = {(0, 0, 0, 0, 0, 1): 1}
J1 = {(0, 1, 0, 0, 1, 0): 2, (0, 0, 2, 0, 0, 0): -1}
J2 = {(0, 0, 1, 0, 0, 1): 2, (0, 0, 0, 2, 0, 0): -1}
F0 = {(1, 0, 0, 0, 2, 4): 1, (0, 1, 1, 1, 1, 3): -1,
      (0, 1, 0, 3, 1, 2): QQ(1) / 3, (0, 0, 2, 3, 0, 2): QQ(1) / 3,
      (0, 0, 1, 5, 0, 1): QQ(-1) / 5, (0, 0, 0, 7, 0, 0): QQ(1) / 35}
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
H = {tuple(e): QQ(c) for (c, e) in HMONO}
GENS = [P, Q, J1, J2, F0, H]


def add(e1, e2):
    return (e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2],
            e1[3] + e2[3], e1[4] + e2[4], e1[5] + e2[5])


def pmul(A, B):
    R = defaultdict(int)
    for a, ca in A.items():
        for b, cb in B.items():
            R[add(a, b)] += ca * cb
    return {k: v for k, v in R.items() if v != 0}


def ppow(A, n):
    R = {(0, 0, 0, 0, 0, 0): 1}
    for _ in range(n):
        R = pmul(R, A)
    return R


def gen_monomials(W):
    out = []

    def rec(i, rem, cur):
        if i == 5:
            if rem % GW[5] == 0:
                out.append(tuple(cur + [rem // GW[5]]))
            return
        for e in range(rem // GW[i] + 1):
            rec(i + 1, rem - e * GW[i], cur + [e])
    rec(0, W, [])
    return out


def expand_genmon(ge):
    R = {(0, 0, 0, 0, 0, 0): 1}
    for i, e in enumerate(ge):
        if e:
            R = pmul(R, ppow(GENS[i], e))
    return R


def excess_qq(w, r):
    W = w + r
    gmB = gen_monomials(W)
    exB = [expand_genmon(ge) for ge in gmB]
    free = []
    seen = set()
    for E in exB:
        for m in E:
            if m[4] < r and m not in seen:
                seen.add(m)
                free.append(m)
    fr = {m: i for i, m in enumerate(free)}
    Mp = Matrix(QQ, len(free), len(gmB), sparse=True)
    for j, E in enumerate(exB):
        for m, c in E.items():
            if m in fr:
                Mp[fr[m], j] = c
    nP = Mp.ncols() - Mp.rank()
    dimCW = len(gen_monomials(W)) - (
        len(gen_monomials(W - 28)) if W >= 28 else 0)
    dimCw = len(gen_monomials(w)) - (
        len(gen_monomials(w - 28)) if w >= 28 else 0)
    return (nP - (len(gmB) - dimCW)) - dimCw, Mp.nrows(), Mp.ncols()


for r, w in ([(1, w) for w in (25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
                               36, 37, 38, 39, 40, 42, 44, 45, 46, 47, 48,
                               49, 50, 51, 52)] +
             [(2, w) for w in (25, 26, 27, 28, 29, 30, 35, 40, 44, 45, 46,
                               47, 48, 49, 50)] +
             [(3, w) for w in (40, 41, 42, 43, 44, 45, 46, 47, 48)]):
    t = cputime()
    try:
        ex, nr, nc = excess_qq(w, r)
        print(f"QQ r={r} w={w} Mprime={nr}x{nc} excess={ex} "
              f"t={cputime()-t:.1f}s", flush=True)
    except Exception as e:
        print(f"QQ r={r} w={w} FAILED {e} t={cputime()-t:.1f}s", flush=True)
