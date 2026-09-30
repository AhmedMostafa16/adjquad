"""Exact QQ membership of F*p^2 in the C5-span at weight 48 (Sage).

Solves G_48 y = t over QQ (G = C5-monomial images, t = F*p^2 image).
Success + verification => F*p^2 in C5 rigorously (the 48-dependency).
Also tests F*p*q, F*q^2 (expect failure = outside).

Run: sage scripts/sage/membership_48.sage
Writes: data/membership_48.log
"""

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

W = 48
dom = []
for e0 in range(W // 8 + 1):
    r0 = W - 8 * e0
    for e1 in range(r0 // 5 + 1):
        r1 = r0 - 5 * e1
        for e2 in range(r1 // 3 + 1):
            r2 = r1 - 3 * e2
            for e3 in range(r2 // 2 + 1):
                rem = r2 - 2 * e3
                for e4 in range(rem + 1):
                    dom.append((e0, e1, e2, e3, e4, rem - e4))
n = len(dom)
ridx = {m: i for i, m in enumerate(dom)}
emit("dimV = %d" % n)

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

Fterms = []
with open("data/witness_w46.txt") as fh:
    for line in fh:
        sp = line.strip().split()
        Fterms.append((QQ(sp[1]), tuple(map(int, sp[0].split(",")))))
F46 = sum(c * prod(R.gen(i)**e for i, e in enumerate(m)) for c, m in Fterms)

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

def sparse_row(poly):
    d = {}
    for exps, c in poly.dict().items():
        i = ridx.get(tuple(exps))
        if i is None:
            raise ValueError("outside V")
        d[i] = d.get(i, 0) + c
    return d

emit("building G rows")
glist = Gmons(W)
Gdict = {}
for r, g in enumerate(glist):
    mon = R.one()
    for base, e in zip(gens, g):
        if e:
            mon = mon * base**e
    for c, v in sparse_row(mon).items():
        Gdict[(r, c)] = v
G = matrix(QQ, len(glist), n, Gdict, sparse=True)
emit("G: %d x %d" % (G.nrows(), n))

for name, T in [("F*p^2", F46 * p**2), ("F*p*q", F46 * p * q), ("F*q^2", F46 * q**2)]:
    t = vector(QQ, n, sparse_row(T))
    try:
        y = G.transpose().solve_right(t)
        ok = (G.transpose() * y == t)
        emit("%s: solve %s, verify %s, nnz(y)=%d" % (name, True, ok, sum(1 for v in y if v != 0)))
        if ok:
            for i, v in enumerate(y):
                if v != 0:
                    emit("    y[%s]=%s" % (glist[i], v))
    except Exception as e:
        emit("%s: NO SOLUTION (%s)" % (name, str(e)[:100]))

with open("data/membership_48.log", "w") as fh:
    fh.write("\n".join(STS) + "\n")
