"""Tower hunt: exact QQ excess vs K/(p^2) prediction + F-product corrections (Task 5).

For each requested weight w (Fibonacci weights 8,5,3,2,1,1):
  N_QQ(w)   = dimV - rank(M)        (exact sparse QQ rank, LinBox)
  img(w)    = rank(G)               (C5-monomial span dim, exact QQ)
  excess(w) = N_QQ(w) - img(w)
  bare(w)   = s_K(w-46) - s_K(w-48)  (K = k[p,q,J1,J2], weights 1,1,6,4)
  corr(w)   = bare(w) + (1 if w >= 60 else 0)   [F46.F0, Task 4]
                      + (1 if w >= 70 else 0)   [F46.H family seed]
  mod2(w)   = bare(w) + s_K(w-60) - s_K(w-62)
                      (two-module prediction: F46.K/(p^2) + F46.F0.K/(p^2);
                       found by the mod-p sweep 58-69 to fit all of 60-69;
                       at w <= 60, mod2 == corr; F.H correction unprobed)
Verdict per weight (against bare, then refined):
  excess == bare -> MATCH-bare (K/(p^2) pattern)
  excess == corr != bare -> MATCH-F-product (deviation from bare accounted
      for by the established F-product direction; classified via J-ideals
      as in Task 4: top(F46.F0) = (18375/4)p^8q^12 outside J_5=(p^10q^12))
  else -> DEVIATION (exact follow-up required: new primitive candidate;
      report weight + a0-degree + top valuations)

The w = 60 row must show the F.F0 direction accounted for (Task 4 theorem:
F46.F0 has a0-degree 5, hence is linearly independent of every F46.mu
direction of a0-degree 4, so excess(60) >= bare(60) + 1 unconditionally).

Pattern reuses scripts/sage/exact_ranks.sage (Vmons/Dcols/Gmons/s6count).
Each weight's block is appended to the log immediately (survives kills).

Run: sage scripts/sage/tower_hunt.sage 58 59 60
     sage scripts/sage/tower_hunt.sage 61 62 [log=PATH] [append=1]
Default weights (pilot): 58 59 60.  Default log: data/tower_hunt.log
(overwrite unless append=1).
"""

import sys
import time
import os

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

def sKcount(w):
    # K-monomial count, coins (1,1,6,4) for (p,q,J1,J2).
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
    for coin in (6, 4):
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s // coin + 1):
                ndp[s] += dp[s - e * coin]
        dp = ndp
    return dp[w]

def bare_pred(w):
    return sKcount(w - 46) - sKcount(w - 48)

def corr_pred(w):
    return bare_pred(w) + (1 if w >= 60 else 0) + (1 if w >= 70 else 0)

def mod2_pred(w):
    # Two-module prediction (mod-p sweep finding): the F.F0 seed grows as
    # its own K/(p^2)-module. J-ideal fingerprint (paper-level, Task-4
    # style): top(F46.F0.mu) = (18375/4)p^8q^12.mu lies in J_5=(p^10q^12)
    # iff v_p(mu) >= 2 -- the same p^2-torsion pattern as F46 itself.
    # The explicit torsion relation F46.F0.p^2 in C5 stays OPEN.
    return bare_pred(w) + sKcount(w - 60) - sKcount(w - 62)

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

weights = []
LOGPATH = "data/tower_hunt.log"
APPEND = False
for x in sys.argv[1:]:
    if x.startswith("log="):
        LOGPATH = x[4:]
    elif x == "append=1":
        APPEND = True
    else:
        weights.append(int(x))
if not weights:
    weights = [58, 59, 60]

if APPEND and os.path.exists(LOGPATH):
    with open(LOGPATH) as fh:
        old = fh.read()
    emit("# tower_hunt (append): existing log kept (%d chars)" % len(old))
else:
    old = ""
    emit("# tower_hunt: exact-QQ excess vs K/(p^2) + F-product corrections [Sage LinBox]")
    emit("# bare(w) = sK(w-46)-sK(w-48); corr(w) = bare + [w>=60 F.F0] + [w>=70 F.H];")
    emit("# mod2(w) = bare + sK(w-60)-sK(w-62) (two-module: F46 and F46.F0 each K/(p^2))")

def flush():
    with open(LOGPATH, "w") as fh:
        fh.write(old + "\n".join(STS) + "\n")

flush()

for W in weights:
    emit("=== weight %d ===" % W)
    t0 = time.time()
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
    t1 = time.time()
    rM = M.rank()
    Nqq = n - rM
    t2 = time.time()
    emit("dimV=%d rank(M)=%d N_QQ=%d (build=%.1fs rank=%.1fs)" % (n, rM, Nqq, t1 - t0, t2 - t1))
    Gdict = {}
    Glist = Gmons(W)
    for r, g in enumerate(Glist):
        mon = R.one()
        for base, e in zip(gens, g):
            if e:
                mon = mon * base**e
        for exps, c in mon.dict().items():
            i = ridx.get(tuple(exps))
            if i is None:
                raise ValueError("image outside V_%d: %s" % (W, (exps,)))
            Gdict[(r, i)] = Gdict.get((r, i), 0) + c
    G = matrix(QQ, len(Glist), n, Gdict, sparse=True)
    t3 = time.time()
    rG = G.rank()
    t4 = time.time()
    emit("C5rows=%d rank(G)=%d (build=%.1fs rank=%.1fs)" % (G.nrows(), rG, t3 - t2, t4 - t3))
    f = s6count(W) - s6count(W - 28)
    b = bare_pred(W)
    c = corr_pred(W)
    m2 = mod2_pred(W)
    exc = Nqq - rG
    emit("formula=%d bare=%d corr=%d mod2=%d excess=N_QQ-rank(G)=%d" % (f, b, c, m2, exc))
    emit("no-second-relation: %s (rank(G)==formula: %s)" % (
        "yes" if rG == f else "NO -- ESCALATE", rG == f))
    if exc == b:
        emit("verdict: MATCH-bare K/(p^2)")
    elif exc == m2:
        emit("verdict: MATCH-F-product (two-module: deviation %d from bare = F.F0.K/(p^2) family sK(%d)-sK(%d)=%d)" % (
            exc - b, W - 60, W - 62, m2 - b))
    elif exc == c:
        emit("verdict: MATCH-F-product-flat (deviation %d from bare accounted for by seed correction only)" % (exc - b))
    else:
        emit("verdict: DEVIATION (excess=%d bare=%d corr=%d mod2=%d; needs exact follow-up: weight+a0deg+top)" % (exc, b, c, m2))
    emit("wall=%.1fs" % (time.time() - t0))
    flush()

emit("# tower_hunt done weights=%s" % weights)
flush()
