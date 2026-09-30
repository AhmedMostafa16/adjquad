"""Exact QQ rank verdicts around the weight-46 excess (Sage, rank-only).

Fast exact decisions via sparse QQ rank (LinBox):
  N_QQ(w)   = dimV - rank(M)
  img(w)    = rank(G)            (C5-monomial span dim)
  excess(w) = N_QQ(w) - img(w)   (>0  <=>  new direction over QQ)
Nullity of stack is NOT computed (right_kernel too slow); explicit
witness extraction is a separate script guided by these ranks.

Run: sage scripts/sage/exact_ranks.sage [w1] [w2] ...
Default weights: 46 47 48
Writes: data/exact_ranks.log
"""

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

def Vmons(w):
    res = []
    for e0 in range(w // 8 + 1):
        r0 = w - 8 * e0
        for e1 in range(r0 // 5 + 1):
            r1 = r0 - 5 * e1
            for e2 in range(r1 // 3 + 1):
                r2 = r1 - 3 * e2
                for e3 in range(r2 // 2 + 1):
                    rem = r2 - 2 * e3
                    for e4 in range(rem + 1):
                        res.append((e0, e1, e2, e3, e4, rem - e4))
    return res

def Dcols(m):
    out = {}
    for i in range(4):
        if m[i]:
            t = list(m)
            t[i] -= 1
            t[i + 1] += 1
            t[i + 2] += 1
            t = tuple(t)
            out[t] = out.get(t, 0) + m[i]
    return out

def Gmons(w):
    res = []
    for f in range(w // 24 + 1):
        r0 = w - 24 * f
        for e in range(r0 // 14 + 1):
            r1 = r0 - 14 * e
            for d in range(r1 // 4 + 1):
                r2 = r1 - 4 * d
                for c in range(r2 // 6 + 1):
                    r3 = r2 - 6 * c
                    for a in range(r3 + 1):
                        res.append((a, r3 - a, c, d, e, f))
    return res

def s6count(w):
    if w < 0:
        return 0
    dp = [0] * (w + 1)
    dp[0] = 1
    for _ in (0, 1):
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s + 1):
                ndp[s] += dp[s - e]
        dp = ndp
    for coin in (6, 4, 14, 24):
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s // coin + 1):
                ndp[s] += dp[s - e * coin]
        dp = ndp
    return dp[w]

R = PolynomialRing(QQ, "a0,a1,a2,a3,a4,a5")
a0, a1, a2, a3, a4, a5 = R.gens()
p, q = a4, a5
J1 = 2 * a1 * a4 - a2**2
J2 = 2 * a2 * a5 - a3**2
F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
      + QQ(1) / 3 * a4 * a5**2 * a3**3 * a1
      + QQ(1) / 3 * a5**2 * a3**3 * a2**2
      - QQ(1) / 5 * a5 * a3**5 * a2 + QQ(1) / 35 * a3**7)
H = (11025*a0**2*a4**4*a5**4 - 22050*a0*a1*a2*a3*a4**3*a5**3
     + 7350*a0*a1*a3**3*a4**3*a5**2 + 7350*a0*a2**2*a3**3*a4**2*a5**2
     - 4410*a0*a2*a3**5*a4**2*a5 + 630*a0*a3**7*a4**2
     + 11025*a1**2*a2**2*a3**2*a4**2*a5**2
     - 7350*a1**2*a2*a3**4*a4**2*a5 + 1225*a1**2*a3**6*a4**2
     + 6720*a1*a2**5*a4*a5**3 - 16800*a1*a2**4*a3**2*a4*a5**2
     + 9450*a1*a2**3*a3**4*a4*a5 - 1540*a1*a2**2*a3**6*a4
     - 2208*a2**7*a5**3 + 4368*a2**6*a3**2*a5**2
     - 2352*a2**5*a3**4*a5 + 385*a2**4*a3**6)
gens = [p, q, J1, J2, F0, H]

import sys
weights = []
for x in sys.argv[1:]:
    if x.startswith("log="):
        LOGPATH = x[4:]
    else:
        weights.append(int(x))
if not weights:
    weights = [46, 47, 48]
LOGPATH = globals().get("LOGPATH", "data/exact_ranks.log")
for W in weights:
    emit("=== weight %d ===" % W)
    dom = Vmons(W)
    n = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    Mdict = {}
    for j, m in enumerate(dom):
        for im, k in Dcols(m).items():
            i = ridx.get(im)
            if i is not None:
                Mdict[(i, j)] = k
    M = matrix(QQ, n, n, Mdict, sparse=True)
    rM = M.rank()
    Nqq = n - rM
    emit("dimV=%d rank(M)=%d N_QQ=%d" % (n, rM, Nqq))
    Gdict = {}
    for r, g in enumerate(Gmons(W)):
        mon = R.one()
        for base, e in zip(gens, g):
            if e:
                mon = mon * base**e
        for exps, c in mon.dict().items():
            i = ridx.get(tuple(exps))
            if i is None:
                raise ValueError("image outside V_%d: %s" % (W, (exps,)))
            Gdict[(r, i)] = Gdict.get((r, i), 0) + c
    G = matrix(QQ, len(Gmons(W)), n, Gdict, sparse=True)
    rG = G.rank()
    emit("C5rows=%d rank(G)=%d" % (G.nrows(), rG))
    f = s6count(W) - s6count(W - 28)
    emit("formula=%d excess=N_QQ-rank(G)=%d" % (f, Nqq - rG))

with open(LOGPATH, "w") as fh:
    fh.write("\n".join(STS) + "\n")
