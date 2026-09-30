"""Exact QQ independence of F-multiples mod C5-span at 47, 48 (Sage).

Checks rank([G; v1; v2]) == rank(G)+2 for (Fp,Fq) at 47 and (Fpq,Fq2)
at 48: proves they span the 2-dim quotients over QQ.

Run: sage scripts/sage/independence_4748.sage
Writes: data/independence_4748.log
"""

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

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

def check(W, T1, T2, n1, n2):
    dom = Vmons(W)
    n = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    def srow(poly):
        d = {}
        for exps, c in poly.dict().items():
            i = ridx.get(tuple(exps))
            if i is None:
                raise ValueError("outside")
            d[i] = d.get(i, 0) + c
        return d
    Gd = {}
    gl = Gmons(W)
    for r, g in enumerate(gl):
        mon = R.one()
        for base, e in zip(gens, g):
            if e:
                mon = mon * base**e
        for c, v in srow(mon).items():
            Gd[(r, c)] = v
    G = matrix(QQ, len(gl), n, Gd, sparse=True)
    rG = G.rank()
    B = matrix(QQ, len(gl) + 2, n, sparse=True)
    B[:len(gl), :] = G
    B[len(gl), :] = vector(QQ, n, srow(T1), sparse=True)
    B[len(gl) + 1, :] = vector(QQ, n, srow(T2), sparse=True)
    rB = B.rank()
    emit("w=%d rank(G)=%d rank(G+%s+%s)=%d independent=%s" % (W, rG, n1, n2, rB, rB == rG + 2))

check(47, F46 * p, F46 * q, "Fp", "Fq")
check(48, F46 * p * q, F46 * q**2, "Fpq", "Fq2")

with open("data/independence_4748.log", "w") as fh:
    fh.write("\n".join(STS) + "\n")
