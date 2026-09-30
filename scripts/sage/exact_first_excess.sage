"""Exact QQ first-excess check: H is the first new generator (Sage).

For weights 15..23, compares exact QQ nullity(M) against rank(G5) where G5
= K[F0]-monomial images (five generators p,q,J1,J2,F0). Equality at every
weight proves ker_w = K[F0]-span for w <= 23, i.e. the weight-24 H is the
first invariant outside K[F0] (with Lean covering w <= 14).

Run: sage scripts/sage/exact_first_excess.sage
Writes: data/exact_first_excess.log
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

def G5mons(w):
    res = []
    for e in range(w // 14 + 1):
        r1 = w - 14 * e
        for d in range(r1 // 4 + 1):
            r2 = r1 - 4 * d
            for c in range(r2 // 6 + 1):
                r3 = r2 - 6 * c
                for a in range(r3 + 1):
                    res.append((a, r3 - a, c, d, e))
    return res

R = PolynomialRing(QQ, "a0,a1,a2,a3,a4,a5")
a0, a1, a2, a3, a4, a5 = R.gens()
p, q = a4, a5
J1 = 2 * a1 * a4 - a2**2
J2 = 2 * a2 * a5 - a3**2
F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
      + QQ(1) / 3 * a4 * a5**2 * a3**3 * a1
      + QQ(1) / 3 * a5**2 * a3**3 * a2**2
      - QQ(1) / 5 * a5 * a3**5 * a2 + QQ(1) / 35 * a3**7)
gens = [p, q, J1, J2, F0]
ok = True
for W in range(15, 24):
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
    Nqq = n - M.rank()
    Gdict = {}
    gl = G5mons(W)
    for r, g in enumerate(gl):
        mon = R.one()
        for base, e in zip(gens, g):
            if e:
                mon = mon * base**e
        for exps, c in mon.dict().items():
            i = ridx.get(tuple(exps))
            if i is None:
                raise ValueError("outside")
            Gdict[(r, i)] = Gdict.get((r, i), 0) + c
    G = matrix(QQ, len(gl), n, Gdict, sparse=True)
    rG = G.rank()
    match = (Nqq == rG)
    ok = ok and match
    emit("w=%d dimV=%d N_QQ=%d rank(G5)=%d %s" % (W, n, Nqq, rG, "OK" if match else "EXCESS"))
emit("FIRST-EXCESS " + ("H-at-24-CONFIRMED" if ok else "EARLIER-DIRECTION-FOUND"))

with open("data/exact_first_excess.log", "w") as fh:
    fh.write("\n".join(STS) + "\n")
