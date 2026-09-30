"""Mixed m=7 lift verdict: full QQ nullspace of a1a2*M + D6(N) = 0.
M over all R-monomials of total degree 7 (B6 6-slots a1..a6);
N over all B6-monomials of degree 8; rows B6-tuples(9).
D6: a1->a2a3, a2->a3a4, a3->a4a5, a4->a5a6, a5,a6->0.
goods_QQ = null(full) - null(N-block): 3 = mixed lifts, 2 = char-p-only.
On lift, prints explicit third (M3, N3) with M3 outside the two exact
directions a5^4a6^3, a5^4a6G4 (rank test) plus Fibonacci weight(s).
Run: sage scripts/cas/check_n6_m7lift.sage (stdout log)
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
# D6 images of variables: a1->a2a3 etc. as exponent pairs (drop, add1, add2)
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

    def rec2(idx, left, cur):
        if idx == 5:
            out.append(tuple(cur + [left]))
            return
        for e in range(left + 1):
            rec2(idx + 1, left - e, cur + [e])
    rec2(0, d, [])
    return out


def D6_tup(m):
    out = defaultdict(QQ)
    for i, (t1, t2) in DRULE.items():
        if m[i]:
            t = list(m)
            t[i] -= 1
            t[t1] += 1
            t[t2] += 1
            out[tuple(t)] += m[i]
    return {k: v for k, v in out.items() if v != 0}


def shift_a1a2(col):
    out = {}
    for e, c in col.items():
        t = list(e)
        t[0] += 1
        t[1] += 1
        out[tuple(t)] = c
    return out


t = cputime()
r7 = R_tuples(7)
print('R_tuples(7) count: %d' % len(r7), flush=True)
Mcols = [shift_a1a2(expand_ge(fe)) for fe in r7]
Ncols = [D6_tup(m) for m in B_tuples(8)]
rows = {}
for C in Mcols + Ncols:
    for m in C:
        if m not in rows:
            rows[m] = len(rows)
print('rows: %d Mcols: %d Ncols: %d' % (len(rows), len(Mcols), len(Ncols)),
      flush=True)
nM, nN = len(Mcols), len(Ncols)
Mfull = Matrix(QQ, len(rows), nM + nN, sparse=True)
for j, C in enumerate(Mcols + Ncols):
    for m, c in C.items():
        Mfull[rows[m], j] = c
MN = Matrix(QQ, len(rows), nN, sparse=True)
for j, C in enumerate(Ncols):
    for m, c in C.items():
        MN[rows[m], j] = c
t = cputime()
null_full = (nM + nN) - Mfull.rank()
null_N = nN - MN.rank()
goods = null_full - null_N
print('null_full = %d null_Nblock = %d goods_QQ = %d t=%.1fs'
      % (null_full, null_N, goods, cputime() - t), flush=True)
if goods == 3:
    print('lift: YES', flush=True)
    K = Mfull.right_kernel()
    basis = K.basis()
    # M-parts of basis vectors are a1a2-SHIFTED (degree 9 rows);
    # unshift (exact: every term carries the +1 shift) to degree 7
    # before comparing with M1, M2.
    M1 = {(0, 0, 0, 0, 4, 3): QQ(1)}
    # M2 = a5^4 a6 G4:
    M2 = pmul(pmul(ppow({(0, 0, 0, 0, 1, 0): QQ(1)}, 4),
                    {(0, 0, 0, 0, 0, 1): QQ(1)}), G4)
    sup = set(M1) | set(M2)
    for v in basis:
        Mp = {}
        for j in range(nM):
            if v[j] != 0:
                for m, c in Mcols[j].items():
                    Mp[m] = Mp.get(m, QQ(0)) + v[j] * c
        Mp = {m: c for m, c in Mp.items() if c != 0}
        if not Mp:
            continue
        assert all(m[0] >= 1 and m[1] >= 1 for m in Mp), 'unshift fault'
        Mu = {(m[0] - 1, m[1] - 1) + m[2:]: c for m, c in Mp.items()}
        mall = list(set(Mu) | set(M1) | set(M2))
        idx = {m: i for i, m in enumerate(mall)}
        A = Matrix(QQ, len(mall), 3, sparse=True)
        for m, c in Mu.items():
            A[idx[m], 0] = c
        for m, c in M1.items():
            A[idx[m], 1] = A[idx[m], 1] + c
        for m, c in M2.items():
            A[idx[m], 2] = A[idx[m], 2] + c
        if A.rank() == 3:
            print('third M3 terms: %d' % len(Mu), flush=True)
            for m in sorted(Mu):
                print('   %s: %s' % (m, Mu[m]), flush=True)
            # TRUE N: preimage monomials (degree 8), NOT D6-images.
            # Fib-24 part solves (D6 preserves Fib weight); assert by
            # direct expansion a1a2*M3 + D6(N24) == 0.
            Bt8 = B_tuples(8)
            Ntrue = {}
            for j in range(nN):
                if v[nM + j] != 0:
                    m = Bt8[j]
                    Ntrue[m] = Ntrue.get(m, QQ(0)) + v[nM + j]
            Ntrue = {m: c for m, c in Ntrue.items() if c != 0}
            FIBW = (8, 5, 3, 2, 1, 1)
            N24 = {m: c for m, c in Ntrue.items()
                   if sum(m[i] * FIBW[i] for i in range(6)) == 24}
            D6N = defaultdict(QQ)
            for m, c in N24.items():
                for mm, cc in D6_tup(m).items():
                    D6N[mm] += c * cc
            D6N = {m: c for m, c in D6N.items() if c != 0}
            LHS = dict(shift_a1a2(Mu))
            for m, c in D6N.items():
                LHS[m] = LHS.get(m, QQ(0)) + c
            LHS = {m: c for m, c in LHS.items() if c != 0}
            assert LHS == {}, 'equation fault'
            print('a1a2M3+D6(N24)==0 exact: PASS', flush=True)
            print('third N3 (Fib-24) terms: %d' % len(N24), flush=True)
            for m in sorted(N24):
                print('   %s: %s' % (m, N24[m]), flush=True)
            wM = {sum(e[i] * FIBW[i] for i in range(6)) for e in Mu}
            print('Fib weights M3: %s N3: 24' % sorted(wM), flush=True)
            break
elif goods == 2:
    print('lift: NO', flush=True)
else:
    print('lift: UNCLEAR', flush=True)
