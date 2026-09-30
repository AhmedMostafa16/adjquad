"""Relation hunt EXACT over QQ (sparse): ker(7-gen map) vs known (S,p2T-E).
Same construction as relation_hunt.sage but exact rationals throughout.
Slow; run bounded ranges. Prints excess per weight (0 = no new relation).
Run: sage scripts/cas/relation_exact.sage [wmin] [wmax] [step]
"""
import sys
WT = (8, 5, 3, 2, 1, 1)
GW = (1, 1, 6, 4, 14, 24, 46)
P = {(0, 0, 0, 0, 1, 0): QQ(1)}
Q = {(0, 0, 0, 0, 0, 1): QQ(1)}
J1 = {(0, 1, 0, 0, 1, 0): QQ(2), (0, 0, 2, 0, 0, 0): QQ(-1)}
J2 = {(0, 0, 1, 0, 0, 1): QQ(2), (0, 0, 0, 2, 0, 0): QQ(-1)}
F0 = {(1, 0, 0, 0, 2, 4): QQ(1), (0, 1, 1, 1, 1, 3): QQ(-1),
      (0, 1, 0, 3, 1, 2): QQ(1)/3, (0, 0, 2, 3, 0, 2): QQ(1)/3,
      (0, 0, 1, 5, 0, 1): QQ(-1)/5, (0, 0, 0, 7, 0, 0): QQ(1)/35}
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
F46 = {}
with open('data/witness_w46.txt') as fh:
    for line in fh:
        sp = line.strip().split()
        F46[tuple(map(int, sp[0].split(',')))] = QQ(sp[1])
GENS = [P, Q, J1, J2, F0, H, F46]


def add(e1, e2):
    return (e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2],
            e1[3] + e2[3], e1[4] + e2[4], e1[5] + e2[5])


def pmul(A, B):
    from collections import defaultdict
    R = defaultdict(int)
    for a, ca in A.items():
        for b, cb in B.items():
            R[add(a, b)] += ca * cb
    return {k: v for k, v in R.items() if v != 0}


def ppow(A, n):
    R = {(0, 0, 0, 0, 0, 0): QQ(1)}
    for _ in range(n):
        R = pmul(R, A)
    return R


def genmons(W, allowF46sq=False):
    out = []

    def rec(i, rem, cur):
        if i == 6:
            if rem == 0:
                out.append(tuple(cur + [0]))
            elif rem == 46:
                out.append(tuple(cur + [1]))
            elif allowF46sq and rem == 92:
                out.append(tuple(cur + [2]))
            return
        for e in range(rem // GW[i] + 1):
            rec(i + 1, rem - e * GW[i], cur + [e])
    rec(0, W, [])
    return out


def expand_ge(ge):
    R = {(0, 0, 0, 0, 0, 0): QQ(1)}
    for i, e in enumerate(ge):
        if e:
            R = pmul(R, ppow(GENS[i], e))
    return R


S_form = [((0, 4, 0, 0, 0, 1, 0), QQ(1)),
          ((0, 0, 0, 0, 2, 0, 0), QQ(-11025)),
          ((0, 2, 1, 5, 0, 0, 0), QQ(-105)),
          ((0, 0, 0, 7, 0, 0, 0), QQ(-9))]
R_form = [((2, 0, 0, 0, 0, 0, 1), QQ(1)),
          ((0, 6, 7, 0, 0, 0, 0), QQ(-40000)),
          ((0, 4, 6, 2, 0, 0, 0), QQ(-193200)),
          ((0, 2, 5, 4, 0, 0, 0), QQ(-325164)),
          ((0, 0, 4, 6, 0, 0, 0), QQ(-148225)),
          ((0, 2, 3, 1, 0, 1, 0), QQ(-840)),
          ((0, 0, 2, 3, 0, 1, 0), QQ(-770)),
          ((0, 0, 0, 0, 0, 2, 0), QQ(-1))]


def tadd(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3],
            a[4] + b[4], a[5] + b[5], a[6] + b[6])


args = sys.argv[1:]
W0 = int(args[0]) if len(args) > 0 else 46
W1 = int(args[1]) if len(args) > 1 else 60
ST = int(args[2]) if len(args) > 2 else 2
w = W0
while w <= W1:
    t = cputime()
    gm = genmons(w)
    gidx = {g: j for j, g in enumerate(gm)}
    ex = [expand_ge(ge) for ge in gm]
    rows = {}
    for E in ex:
        for m in E:
            if m not in rows:
                rows[m] = len(rows)
    M = Matrix(QQ, len(rows), len(gm), sparse=True)
    for j, E in enumerate(ex):
        for m, c in E.items():
            M[rows[m], j] = c
    nullM = len(gm) - M.rank()
    kcols = []
    if w >= 28:
        for ge in genmons(w - 28):
            d = {}
            for e, c in S_form:
                k = tadd(e, ge)
                if k in gidx:
                    d[gidx[k]] = d.get(gidx[k], 0) + c
            kcols.append({k: v for k, v in d.items() if v != 0})
    if w >= 48:
        for ge in genmons(w - 48):
            d = {}
            for e, c in R_form:
                k = tadd(e, ge)
                if k in gidx:
                    d[gidx[k]] = d.get(gidx[k], 0) + c
            kcols.append({k: v for k, v in d.items() if v != 0})
    K = Matrix(QQ, len(gm), len(kcols), sparse=True)
    for j, d in enumerate(kcols):
        for i, c in d.items():
            K[i, j] = c
    rK = K.rank()
    print(f"QQ w={w} A={len(rows)} gen={len(gm)} null={nullM} known={rK} "
          f"excess={nullM - rK} t={cputime()-t:.1f}s", flush=True)
    w += ST
