"""m=14 finish-line gate: Q_14 = M_14 / (K6 * four exact dirs)_14, exact QQ.
Four frozen dirs (M,N): d1 H20-dir, d2 D2-dir, d3 M3-dir, d4 M8-dir,
each equation re-asserted by direct expansion. Rows B6-tuples(16);
M-cols R_tuples(14) + HB*R_tuples(4) shifted; N-cols D6(B_tuples(15)).
Verdict: quot-dim 0 = closure window through 14; >0 = first failure
(recorded, no hunt follows). THE DENOMINATOR CAMPAIGN ENDS HERE.
Run: sage scripts/cas/check_n6_m14.py (stdout log)
"""
from collections import defaultdict


def Q(a, b=1):
    return QQ(a) / b


FIBW6 = (8, 5, 3, 2, 1, 1)
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
ND1 = {(0, 0, 4, 4, 0, 0): Q(-19, 480),
       (0, 0, 5, 2, 0, 1): Q(293, 1800),
       (0, 0, 6, 0, 0, 2): Q(-49, 450),
       (0, 1, 2, 4, 1, 0): Q(19, 120),
       (0, 1, 3, 2, 1, 1): Q(-59, 90),
       (0, 1, 4, 0, 1, 2): Q(59, 180),
       (0, 2, 0, 4, 2, 0): Q(-1, 8),
       (0, 2, 1, 2, 2, 1): Q(1, 2),
       (1, 0, 0, 5, 2, 0): Q(-1, 15),
       (1, 0, 1, 3, 2, 1): Q(1, 3),
       (1, 1, 0, 1, 3, 2): Q(-1, 1)}
ND2 = {(0, 0, 6, 2, 0, 0): Q(-1, 72),
       (0, 0, 7, 0, 0, 1): Q(5, 756),
       (0, 1, 4, 2, 1, 0): Q(1, 12),
       (0, 1, 5, 0, 1, 1): Q(-1, 54),
       (0, 2, 2, 2, 2, 0): Q(-1, 9),
       (0, 2, 3, 0, 2, 1): Q(-1, 27),
       (1, 0, 2, 3, 2, 0): Q(-1, 9),
       (1, 1, 0, 3, 3, 0): Q(2, 9),
       (1, 1, 1, 1, 3, 1): Q(1, 3),
       (2, 0, 0, 0, 4, 2): Q(-7, 6)}
M3 = {(0, 0, 0, 4, 2, 1): Q(1),
      (0, 0, 1, 2, 2, 2): Q(-4),
      (0, 0, 2, 0, 2, 3): Q(-16, 21),
      (0, 1, 0, 0, 3, 3): Q(200, 21)}
N3 = {(0, 2, 2, 4, 0, 0): Q(-3, 14),
      (0, 2, 3, 2, 0, 1): Q(19, 21),
      (0, 3, 0, 4, 1, 0): Q(3, 7),
      (0, 3, 1, 2, 1, 1): Q(-12, 7),
      (0, 3, 2, 0, 1, 2): Q(-152, 63),
      (0, 4, 0, 0, 2, 2): Q(40, 9),
      (1, 0, 2, 5, 0, 0): Q(3, 7),
      (1, 0, 3, 3, 0, 1): Q(-38, 21),
      (1, 1, 0, 5, 1, 0): Q(-6, 7),
      (1, 1, 1, 3, 1, 1): Q(23, 7),
      (1, 1, 2, 1, 1, 2): Q(38, 7),
      (1, 2, 0, 1, 2, 2): Q(-200, 21),
      (2, 0, 0, 2, 2, 2): Q(7, 6),
      (2, 0, 1, 0, 2, 3): Q(-7, 3)}
M8 = {(0, 0, 0, 4, 4, 0): Q(1),
      (0, 0, 1, 2, 4, 1): Q(-4),
      (0, 0, 2, 0, 4, 2): Q(17, 3),
      (0, 1, 0, 0, 5, 2): Q(-10, 3)}
N8 = {(0, 0, 7, 2, 0, 0): Q(1, 35),
      (0, 1, 5, 2, 1, 0): Q(-1, 5),
      (0, 1, 6, 0, 1, 1): Q(-2, 35),
      (0, 2, 3, 2, 2, 0): Q(1, 3),
      (0, 2, 4, 0, 2, 1): Q(13, 35),
      (0, 3, 2, 0, 3, 1): Q(-121, 315),
      (0, 4, 0, 0, 4, 1): Q(-202, 315),
      (1, 0, 3, 3, 2, 0): Q(1, 3),
      (1, 1, 1, 3, 3, 0): Q(-1, 1),
      (1, 1, 2, 1, 3, 1): Q(-1, 1),
      (1, 2, 0, 1, 4, 1): Q(10, 3),
      (2, 0, 0, 2, 4, 1): Q(7, 6),
      (2, 0, 1, 0, 4, 2): Q(-7, 3)}
DRULE = {0: (1, 2), 1: (2, 3), 2: (3, 4), 3: (4, 5)}


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


def padd(A, B, s=1):
    R = defaultdict(QQ, A)
    for k, v in B.items():
        R[k] += s * v
    return {k: v for k, v in R.items() if v != 0}


def D6dict(P):
    R = defaultdict(QQ)
    for m, c in P.items():
        for i, (t1, t2) in DRULE.items():
            if m[i]:
                t = list(m)
                t[i] -= 1
                t[t1] += 1
                t[t2] += 1
                R[tuple(t)] += c * m[i]
    return {k: v for k, v in R.items() if v != 0}


def shift_a1a2(col):
    out = {}
    for e, c in col.items():
        t = list(e)
        t[0] += 1
        t[1] += 1
        out[tuple(t)] = c
    return out


def fibw(P):
    return {sum(e[i] * FIBW6[i] for i in range(6)) for e in P}


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


def B_tuples(d):
    out = []

    def rec(idx, left, cur):
        if idx == 5:
            out.append(tuple(cur + [left]))
            return
        for e in range(left + 1):
            rec(idx + 1, left - e, cur + [e])
    rec(0, d, [])
    return out


def K6mons(d):
    out = [expand_ge(fe) for fe in R_tuples(d)]
    if d >= 10:
        for fe in R_tuples(d - 10):
            out.append(pmul(HB, expand_ge(fe)))
    return out


def vecmat(vecs, universe):
    idx = {m: i for i, m in enumerate(universe)}
    M = Matrix(QQ, len(universe), len(vecs), sparse=True)
    for j, V in enumerate(vecs):
        for m, c in V.items():
            M[idx[m], j] = c
    return M


t = cputime()
print('base self-checks:', flush=True)
assert D6dict(HB) == {}, 'HB fault'
print('PASS D6(HB)=0', flush=True)
MD1 = {(0, 0, 0, 0, 4, 3): QQ(1)}
MD2 = pmul(pmul(ppow({(0, 0, 0, 0, 1, 0): QQ(1)}, 4),
                 {(0, 0, 0, 0, 0, 1): QQ(1)}), G4)
DIRS = [(MD1, ND1, 7), (MD2, ND2, 7), (M3, N3, 7), (M8, N8, 8)]
for k, (Md, Nd, md) in enumerate(DIRS):
    assert padd(shift_a1a2(Md), D6dict(Nd)) == {}, 'dir eq fault %d' % k
    print('PASS dir%d eq (deg %d)' % (k + 1, md), flush=True)
print('base checks t=%.1fs' % (cputime() - t), flush=True)
m = 14
t = cputime()
Mcols = [shift_a1a2(expand_ge(fe)) for fe in R_tuples(m)]
for fe in R_tuples(m - 10):
    Mcols.append(shift_a1a2(pmul(HB, expand_ge(fe))))
Bt1 = B_tuples(m + 1)
Ncols = [D6dict({mm: QQ(1)}) for mm in Bt1]
rows = {}
for C in Mcols + Ncols:
    for mm in C:
        if mm not in rows:
            rows[mm] = len(rows)
nM, nN = len(Mcols), len(Ncols)
print('rows: %d Mcols: %d Ncols: %d' % (len(rows), nM, nN), flush=True)
Mf = Matrix(QQ, len(rows), nM + nN, sparse=True)
for j, C in enumerate(Mcols + Ncols):
    for mm, c in C.items():
        Mf[rows[mm], j] = c
MN = Matrix(QQ, len(rows), nN, sparse=True)
for j, C in enumerate(Ncols):
    for mm, c in C.items():
        MN[rows[mm], j] = c
nullF = (nM + nN) - Mf.rank()
nullN = nN - MN.rank()
goods = nullF - nullN
print('nullF = %d nullN = %d goods_QQ(14) = %d' % (nullF, nullN, goods),
      flush=True)
K = Mf.right_kernel()
Mpairs = []
for v in K.basis():
    Mp, Np = {}, {}
    for j in range(nM):
        if v[j] != 0:
            for mm, c in Mcols[j].items():
                Mp[mm] = Mp.get(mm, QQ(0)) + v[j] * c
    for j in range(nN):
        if v[nM + j] != 0:
            mm = Bt1[j]
            Np[mm] = Np.get(mm, QQ(0)) + v[nM + j]
    Mp = {mm: c for mm, c in Mp.items() if c != 0}
    Np = {mm: c for mm, c in Np.items() if c != 0}
    if Mp:
        assert all(mm[0] >= 1 and mm[1] >= 1 for mm in Mp)
        Mu = {(mm[0] - 1, mm[1] - 1) + mm[2:]: c
              for mm, c in Mp.items()}
        Mpairs.append((Mu, Np))
basis, Nbasis = [], []
uni = list({mm for Mu, Np in Mpairs for mm in Mu})
print('Mpairs (nonempty M): %d' % len(Mpairs), flush=True)
print('dim-span all Mparts: %d'
      % vecmat([Mu for Mu, Np in Mpairs], uni).rank(), flush=True)
for Mu, Np in Mpairs:
    if vecmat(basis + [Mu], uni).rank() == len(basis) + 1:
        basis.append(Mu)
        Nbasis.append(Np)
assert len(basis) == goods, 'projection fault'
Gvecs = []
for (Md, Nd, md) in DIRS:
    for mu in K6mons(m - md):
        Gvecs.append(pmul(mu, Md))
uni2 = list({mm for Mu in basis for mm in Mu} |
            {mm for G in Gvecs for mm in G})
gdim = vecmat(Gvecs, uni2).rank()
print('gendim = %d' % gdim, flush=True)
rGS = vecmat(Gvecs + basis, uni2).rank()
print('quot-dim = %d' % (rGS - gdim), flush=True)
res = []
if rGS > gdim:
    for Mu, Np in zip(basis, Nbasis):
        if vecmat(Gvecs + [Mu], uni2).rank() == vecmat(Gvecs, uni2).rank():
            continue
        assert padd(shift_a1a2(Mu), D6dict(Np)) == {}, 'residual eq fault'
        res.append((Mu, Np))
        Gvecs = Gvecs + [Mu]
print('quot-dim = %d' % len(res), flush=True)
for Mu, Np in res:
    print('residual M terms: %d N terms: %d Fib M: %s' %
          (len(Mu), len(Np), sorted(fibw(Mu))), flush=True)
    for mm in sorted(Mu):
        print('   M %s: %s' % (mm, Mu[mm]), flush=True)
    for mm in sorted(Np):
        print('   N %s: %s' % (mm, Np[mm]), flush=True)
print('Q14 = 0' if not res else 'Q14 != 0 (%d new)' % len(res), flush=True)
print('m14 DONE', flush=True)
