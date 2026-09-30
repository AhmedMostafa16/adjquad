"""Exact QQ verdict on the weight-46 excess (Sage).

Decides, with exact rational arithmetic, whether ker(D5|V_46) strictly
exceeds the C5-monomial span:
  nullity(stack(M, G)) = dim(ker M cap rowspace(G)^perp)
  = 0  <=> every weight-46 invariant is in the C5-span (mod-p excess
           was a rank-drop artifact),
  > 0  <=> a genuine new invariant direction over QQ (Conj 11.2 false),
           with explicit null vectors = polynomials outside C5.
Also reports exact nullity(M) = N_QQ(46).

Run: sage scripts/sage/exact_w46.sage
Writes: data/exact_w46.log
"""

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

WVAR = [8, 5, 3, 2, 1, 1]   # Fibonacci weights a0..a5
WGEN = [1, 1, 6, 4, 14, 24]  # generator weights p,q,J1,J2,F0,H
W = 46

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
    # D(a_i) = a_{i+1} a_{i+2} for i<=3, else 0. Returns {image: coeff}.
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
    # exponent tuples over (p,q,J1,J2,F0,H)
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

emit("building V basis")
dom = Vmons(W)
n = len(dom)
ridx = {m: i for i, m in enumerate(dom)}
emit("dim V_46 = %d" % n)

emit("building D matrix (sparse QQ)")
Mdict = {}
for j, m in enumerate(dom):
    for im, k in Dcols(m).items():
        i = ridx.get(im)
        if i is not None:
            Mdict[(i, j)] = k
M = matrix(QQ, n, n, Mdict, sparse=True)
emit("D nonzeros = %d" % len(Mdict))

from sage.matrix.matrix_space import MatrixSpace
emit("exact rank(M) ...")
rM = M.rank()
emit("rank(M) = %d  nullity(M) = N_QQ(46) = %d" % (rM, n - rM))

# six-generator monomial images
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

def expvec(poly):
    # sparse row dict {col: coeff} of poly in V basis
    d = {}
    for exps, c in poly.dict().items():
        i = ridx.get(tuple(exps))
        if i is None:
            raise ValueError("monomial outside V_46: %s" % (exps,))
        d[i] = d.get(i, 0) + c
    return d

emit("building C5-monomial rows")
grows = []
for g in Gmons(W):
    mon = R.one()
    for base, e in zip(gens, g):
        if e:
            mon = mon * base**e
    grows.append(expvec(mon))
emit("C5 monomial images: %d rows" % len(grows))

emit("stacking and computing nullity(stack) ...")
Sdict = dict(Mdict)
for r, d in enumerate(grows):
    for c, v in d.items():
        Sdict[(n + r, c)] = v
S = matrix(QQ, n + len(grows), n, Sdict, sparse=True)
NS = S.right_kernel()
emit("nullity(stack) = %d" % NS.dimension())
if NS.dimension() == 0:
    emit("VERDICT: no new direction over QQ at weight 46 (mod-p excess was artifact)")
else:
    emit("VERDICT: NEW DIRECTION over QQ at weight 46 (Conjecture 11.2 FALSE as stated)")
    v = NS.basis()[0]
    nz = [(i, v[i]) for i in range(n) if v[i] != 0]
    emit("witness support size = %d" % len(nz))
    a0degs = sorted(set(dom[i][0] for i, _ in nz))
    emit("witness a0-degrees present = %s" % a0degs)
    top = max(dom[i][0] for i, _ in nz)
    emit("witness max a0-degree = %d" % top)
    topterms = [(dom[i], v[i]) for i, _ in nz if dom[i][0] == top]
    emit("witness top-a0 terms (expvec, coeff):")
    for t in topterms[:40]:
        emit("  %s  %s" % (t[0], t[1]))

with open("data/exact_w46.log", "w") as fh:
    fh.write("\n".join(STS) + "\n")
