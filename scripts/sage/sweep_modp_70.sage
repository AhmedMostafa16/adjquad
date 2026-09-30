"""Mod-p nullity sweep at weights 70+ (Sage, LinBox over GF(1000003)).

The dict-based hunt_high_weights.py is infeasible past dimV~100k; sparse
LinBox rank over a finite field extends the frontier. Nullity mod p is an
UPPER bound on QQ nullity: agreement with prediction = consistency
(evidence only); excess ABOVE prediction = candidate new primitive.

Compares N_p(w) against formula s6(w)-s6(w-28) and the three-module
prediction P(w) = [sK(w-46)-sK(w-48)] + [sK(w-60)-sK(w-62)]
+ [sK(w-70)-sK(w-72)].

Run: sage scripts/sage/sweep_modp_70.sage [w1] [w2] ...
Writes: data/sweep_modp_70.log (appended per weight)
"""

import sys

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

P = 1000003
F = GF(P)

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

def sK(w):
    if w < 0:
        return 0
    n = 0
    for d in range(w // 6 + 1):
        for c in range((w - 6 * d) // 4 + 1):
            n += w - 6 * d - 4 * c + 1
    return n

def pred(w):
    return sum(sK(w - wi) - sK(w - wi - 2) for wi in (46, 60, 70))

weights = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [70]
for W in weights:
    import time
    t0 = time.time()
    dom = Vmons(W)
    n = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    Mdict = {}
    for j, m in enumerate(dom):
        for im, k in Dcols(m).items():
            i = ridx.get(im)
            if i is not None:
                Mdict[(i, j)] = k % P
    M = matrix(F, n, n, Mdict, sparse=True)
    rM = M.rank()
    Np = n - rM
    f = s6count(W) - s6count(W - 28)
    p = pred(W)
    emit("w=%d dimV=%d N_p=%d formula=%d excess=%d pred=%d %s (%.0fs)"
         % (W, n, Np, f, Np - f, p,
            "MATCH" if Np - f == p else "DEVIATION", time.time() - t0))

with open("data/sweep_modp_70.log", "a") as fh:
    fh.write("\n".join(STS) + "\n")
