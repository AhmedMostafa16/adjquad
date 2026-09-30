"""Audit: independent rank computations for the m=14 matrices.
Mf (full system), MN (N-block): QQ rank via several algorithms,
transpose-rank (independent code path), and mod-p=1000003 rank
(rank_p <= rank_QQ always: a HIGHER mod-p rank disproves a QQ rank).
Same construction as check_n6_m14.py (frozen data copied verbatim).
Run: sage scripts/cas/check_n6_m14audit.sage (stdout log)
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
DRULE = {0: (1, 2), 1: (2, 3), 2: (3, 4), 3: (4, 5)}
PRIME = 1000003


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


def modp_nullity(rows, cols):
    n, p = len(rows), len(cols)
    ridx = {m: i for i, m in enumerate(rows)}
    M = [defaultdict(int) for _ in range(n)]
    for j, col in enumerate(cols):
        for nm, k in col.items():
            r = ridx.get(nm)
            if r is not None:
                M[r][j] = (M[r].get(j, 0) + k) % PRIME
    rank = 0
    for ccol in range(p):
        pv = None
        for r in range(rank, n):
            if M[r].get(ccol, 0) != 0:
                pv = r
                break
        if pv is None:
            continue
        M[rank], M[pv] = M[pv], M[rank]
        inv = pow(M[rank][ccol], PRIME - 2, PRIME)
        for cc in list(M[rank]):
            M[rank][cc] = (inv * M[rank][cc]) % PRIME
        for r in range(n):
            if r == rank:
                continue
            f = M[r].get(ccol, 0)
            if f == 0:
                continue
            for cc, vv in list(M[rank].items()):
                M[r][cc] = (M[r].get(cc, 0) - f * vv) % PRIME
                if M[r][cc] == 0:
                    del M[r][cc]
        M[rank].pop(ccol, None)
        rank += 1
    return p - rank


def to_modp_col(C):
    out = {}
    for m, c in C.items():
        num = int(c.numerator()) % PRIME
        den = int(c.denominator()) % PRIME
        v = (num * pow(den, PRIME - 2, PRIME)) % PRIME
        if v:
            out[m] = v
    return out


t = cputime()
m = 14
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
print('rows: %d Mcols: %d Ncols: %d t=%.1fs'
      % (len(rows), nM, nN, cputime() - t), flush=True)
Mf = Matrix(QQ, len(rows), nM + nN, sparse=True)
for j, C in enumerate(Mcols + Ncols):
    for mm, c in C.items():
        Mf[rows[mm], j] = c
MN = Matrix(QQ, len(rows), nN, sparse=True)
for j, C in enumerate(Ncols):
    for mm, c in C.items():
        MN[rows[mm], j] = c
print('built t=%.1fs' % (cputime() - t), flush=True)
t = cputime()
n_tr = MN.transpose().rank()
print('MN.T.rank = %d t=%.1fs' % (n_tr, cputime() - t), flush=True)
t = cputime()
try:
    r_lin = Mf.rank(algorithm='linbox')
    print('Mf.rank linbox = %d t=%.1fs' % (r_lin, cputime() - t),
          flush=True)
except Exception as e:
    print('Mf linbox FAILED: %s' % e, flush=True)
t = cputime()
try:
    n_lin = MN.rank(algorithm='linbox')
    print('MN.rank linbox = %d t=%.1fs' % (n_lin, cputime() - t),
          flush=True)
except Exception as e:
    print('MN linbox FAILED: %s' % e, flush=True)
print('probe DONE', flush=True)
n_def = MN.rank()
print('MN.rank default = %d t=%.1fs' % (n_def, cputime() - t), flush=True)
t = cputime()
try:
    n_sing = MN.rank(algorithm='singular')
    print('MN.rank singular = %d t=%.1fs' % (n_sing, cputime() - t),
          flush=True)
except Exception as e:
    print('MN singular FAILED: %s' % e, flush=True)
t = cputime()
rowlist = list(rows)
nullpF = modp_nullity(rowlist, [to_modp_col(C) for C in Mcols + Ncols])
print('mod-p nullF = %d t=%.1fs' % (nullpF, cputime() - t), flush=True)
t = cputime()
nullpN = modp_nullity(rowlist, [to_modp_col(C) for C in Ncols])
print('mod-p nullN = %d t=%.1fs' % (nullpN, cputime() - t), flush=True)
print('audit DONE', flush=True)
