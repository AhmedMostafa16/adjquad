"""Exact tower verification at weights 70+ via squeeze (Sage).

For each weight w: (1) rank_QQ(G) on C5-monomial images (expect formula);
(2) rank_QQ(stack(G, Ffam)) on C5 + explicit F-family monomials
(expect formula + P(w)); (3) nullity mod p of D|V_w via LinBox
(expect formula + P(w)). If all three hold, the squeeze
  formula + P(w) <= N_QQ(w) <= N_p(w) = formula + P(w)
proves excess(w) = P(w) EXACTLY: (2) gives QQ-independent kernel vectors
(lower bound), (3) gives the universal upper bound N_QQ <= N_p.
Any failure is falsifier data (deviation above/below prediction).

F-family monomials (all D-closed: D(F46)=D(F0)=D(H)=D(mu)=0):
  Fam1: F46*mu, mu reps of K/(p^2) at weight w-46
  Fam2: (F46*F0)*mu, mu reps at weight w-60
  Fam3: (F46*H)*mu, mu reps at weight w-70
K/(p^2) reps = K-monomials in (p,q,J1,J2) weights (1,1,6,4) with p-exp<=1.
F46 = cleared integral form from data/witness_w46.txt (nonzero scalar OK/QQ).

Run: sage scripts/sage/tower_verify.sage [w1] [w2] ...
Writes: data/tower_verify.log (appended)
"""

import sys

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)
    with open("data/tower_verify.log", "a") as fh:
        fh.write(s + "\n")

import os
STAGE = os.environ.get("TOWER_STAGE", "all")

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

def Kmons(d):
    # (p,q,J1,J2) exponents, weights (1,1,6,4)
    res = []
    for c in range(d // 6 + 1):
        r1 = d - 6 * c
        for u in range(r1 // 4 + 1):
            r2 = r1 - 4 * u
            for a in range(r2 + 1):
                res.append((a, r2 - a, c, u))
    return res

def Kmodp2mons(d):
    return [g for g in Kmons(d) if g[0] <= 1]

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
Kgens = [p, q, J1, J2]
Fterms = []
with open("data/witness_w46.txt") as fh:
    for line in fh:
        sp = line.strip().split()
        Fterms.append((QQ(sp[1]), tuple(map(int, sp[0].split(",")))))
F46 = sum(c * prod(R.gen(i)**e for i, e in enumerate(m)) for c, m in Fterms)
F46F0 = F46 * F0
F46H = F46 * H

weights = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [70]
for W in weights:
    emit("=== weight %d ===" % W)
    dom = Vmons(W)
    n = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    emit("dimV=%d" % n)

    def srow(poly):
        d = {}
        for exps, c in poly.dict().items():
            i = ridx.get(tuple(exps))
            if i is None:
                raise ValueError("image outside V_%d" % W)
            d[i] = d.get(i, 0) + c
        return d

    # (1) C5-monomial images over QQ
    if STAGE in ("all", "qq"):
        gl = Gmons(W)
        Gdict = {}
        pows = {}
        def gpow(idx, base, e):
            key = (idx, e)
            if key not in pows:
                pows[key] = base**e
            return pows[key]
        for r, g in enumerate(gl):
            mon = R.one()
            for idx, (base, e) in enumerate(zip(gens, g)):
                if e:
                    mon = mon * gpow(idx, base, e)
            for c, v in srow(mon).items():
                Gdict[(r, c)] = v
        G = matrix(QQ, len(gl), n, Gdict, sparse=True)
        rG = G.rank()
        formula = s6count(W) - s6count(W - 28)
        emit("C5rows=%d rank(G)=%d formula=%d %s"
             % (len(gl), rG, formula, "NOR2NDREL" if rG == formula else "SECOND-RELATION?"))
    else:
        gl = Gmons(W)
        formula = s6count(W) - s6count(W - 28)
        rG = None
    # (2) F-family rows over QQ
    if STAGE in ("all", "qq"):
        fams = ([(F46, W - 46)] if W >= 46 else []) + \
               ([(F46F0, W - 60)] if W >= 60 else []) + \
               ([(F46H, W - 70)] if W >= 70 else [])
        frows = []
        for Fbase, dw in fams:
            for g in Kmodp2mons(dw):
                mon = Fbase
                for idx, (base, e) in enumerate(zip(Kgens, g)):
                    if e:
                        mon = mon * gpow(10 + idx, base, e)
                frows.append(srow(mon))
        emit("F-family rows=%d (pred excess=%d)" % (len(frows), pred(W)))
        Sdict = dict(Gdict)
        for k, d in enumerate(frows):
            for c, v in d.items():
                Sdict[(len(gl) + k, c)] = v
        S = matrix(QQ, len(gl) + len(frows), n, Sdict, sparse=True)
        rS = S.rank()
        emit("rank(stack)=%d formula+P=%d %s"
             % (rS, formula + pred(W), "SPAN" if rS == formula + pred(W) else "SHORT"))
    else:
        rS = None
    # (3) mod-p nullity via LinBox
    if STAGE in ("all", "modp"):
        Mdict = {}
        for j, m in enumerate(dom):
            for im, k in Dcols(m).items():
                i = ridx.get(im)
                if i is not None:
                    Mdict[(i, j)] = k % P
        Mp = matrix(F, n, n, Mdict, sparse=True)
        Np = n - Mp.rank()
        emit("rank_p(M) nullity N_p=%d formula+P=%d %s"
             % (Np, formula + pred(W), "MEET" if Np == formula + pred(W) else "ABOVE"))
        Np_out = Np
    else:
        Np_out = None
    if STAGE == "all":
        if rG == formula and rS == formula + pred(W) and Np_out == formula + pred(W):
            emit("VERDICT w=%d: EXACT excess=%d (squeeze lower+upper meet)" % (W, pred(W)))
        else:
            emit("VERDICT w=%d: FALSIFIER DATA (see three lines above)" % W)
    elif STAGE == "qq":
        if rG == formula and rS == formula + pred(W):
            emit("VERDICT w=%d: LOWER meets prediction (upper open)" % W)
        else:
            emit("VERDICT w=%d: FALSIFIER DATA (lower does not meet)" % W)
    elif STAGE == "modp":
        emit("VERDICT w=%d: mod-p line recorded (see N_p above)" % W)
