"""Bounded denominator module through m=12 (N=6, exact QQ).
For each m in 7..12: M_m = unshifted M-projection of ker(a1a2*M+D6(N)=0);
G_m = cumulative K6-span of exact dirs below m (starts: H20-dir, D2-dir,
M3); Q_m = complement with (M,N) witnesses by linearity; new residuals
join the exact dirs. Ends with joint-independence verdict.
Base witnesses re-verified in-script by direct expansion.
Run: sage scripts/cas/check_n6_denmod.py (stdout log)
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
H20A0FREE = {(0, 0, 4, 4, 0, 0): Q(-19, 480),
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
D2N = {(0, 0, 6, 2, 0, 0): Q(-1, 72),
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
assert D6dict(HB) == {}, 'HB invariance fault'
print('PASS D6(HB)=0', flush=True)
M_d1 = {(0, 0, 0, 0, 4, 3): QQ(1)}
assert padd(shift_a1a2(M_d1), D6dict(H20A0FREE)) == {}, 'H20 eq fault'
print('PASS a1a2M_d1+D6(N_d1)=0', flush=True)
M_d2 = pmul(pmul(ppow({(0, 0, 0, 0, 1, 0): QQ(1)}, 4),
                  {(0, 0, 0, 0, 0, 1): QQ(1)}), G4)
assert padd(shift_a1a2(M_d2), D6dict(D2N)) == {}, 'D2 eq fault'
print('PASS a1a2M_d2+D6(N_d2)=0', flush=True)
assert padd(shift_a1a2(M3), D6dict(N3)) == {}, 'M3 eq fault'
print('PASS a1a2M3+D6(N3)=0', flush=True)
dirs = [(M_d1, H20A0FREE, 7), (M_d2, D2N, 7), (M3, N3, 7)]
print('base checks t=%.1fs' % (cputime() - t), flush=True)
allgen = []
for m in range(7, 13):
    t = cputime()
    Mcols = [shift_a1a2(expand_ge(fe)) for fe in R_tuples(m)]
    if m >= 10:
        for fe in R_tuples(m - 10):
            Mcols.append(shift_a1a2(pmul(HB, expand_ge(fe))))
    Bt1 = B_tuples(m + 1)
    Ncols = []
    Npre = []
    Dd = {}
    for mm in Bt1:
        Dd[mm] = D6dict({mm: QQ(1)})
        Ncols.append(Dd[mm])
    rows = {}
    for C in Mcols + Ncols:
        for mm in C:
            if mm not in rows:
                rows[mm] = len(rows)
    nM, nN = len(Mcols), len(Ncols)
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
    if m == 7:
        assert goods == 3, 'm7 baseline fault'
    K = Mf.right_kernel()
    # M-projection basis with true N-parts (preimages)
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
    # independent M-subset (greedy), N carried along
    basis, Nbasis = [], []
    uni = list({mm for Mu, Np in Mpairs for mm in Mu})
    for Mu, Np in Mpairs:
        test = vecmat(basis + [Mu], uni)
        if test.rank() == len(basis) + 1:
            basis.append(Mu)
            Nbasis.append(Np)
    assert len(basis) == goods, 'projection fault m=%d' % m
    # generated subspace from exact dirs below m
    Gvecs = []
    for (Md, Nd, md) in dirs:
        if md < m:
            for mu in K6mons(m - md):
                Gvecs.append(pmul(mu, Md))
    uni2 = list({mm for Mu in basis for mm in Mu} |
                {mm for G in Gvecs for mm in G})
    gdim = vecmat(Gvecs, uni2).rank() if Gvecs else 0
    # residuals: basis elements adding rank beyond G
    res, resN = [], []
    Gcur = Gvecs
    for Mu, Np in zip(basis, Nbasis):
        if vecmat(Gcur + [Mu], uni2).rank() == vecmat(Gcur, uni2).rank():
            continue
        res.append(Mu)
        resN.append(Np)
        Gcur = Gcur + [Mu]
    # verify each residual equation by direct expansion
    for Mu, Np in zip(res, resN):
        assert padd(shift_a1a2(Mu), D6dict(Np)) == {}, \
            'residual eq fault m=%d' % m
    for Mu, Np in zip(res, resN):
        dirs.append((Mu, Np, m))
        allgen.append(Mu)
    wres = []
    for Mu in res:
        wres.append(sorted(fibw(Mu)))
    print('m=%d goods=%d gendim=%d new=%d Fib(res)=%s t=%.1fs'
          % (m, goods, gdim, len(res), wres, cputime() - t), flush=True)
# joint independence of all generator M-vectors through 12
uniA = list({mm for Mu in allgen for mm in Mu})
print('joint generators: %d rank %d' % (len(allgen),
      vecmat(allgen, uniA).rank()), flush=True)
print('denmod12 DONE', flush=True)
