"""Exact QQ extraction of the weight-46 new invariant (Sage).

Solves M[:, S] x = 0 over QQ on the mod-p support S (79 monomials,
data/vbar_w46.txt). A nontrivial QQ solution is an explicit invariant
candidate; cleared to integral, verified D(F)=0 exactly, fingerprinted
(a0-degree, top coefficient, p/q valuations vs P-top/Q-top-strong).

Run: sage scripts/sage/extract_w46.sage
Writes: data/witness_w46.log, data/witness_w46.txt (integral monomial list)
"""

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

W = 46
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

supp = []
with open("data/vbar_w46.txt") as fh:
    for line in fh:
        parts = line.strip().split()
        supp.append(tuple(map(int, parts[0].split(","))))
S = sorted(set(ridx[m] for m in supp))
emit("support size = %d" % len(S))

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

MS = {}
sidx = {c: k for k, c in enumerate(S)}
for k, j in enumerate(S):
    for im, val in Dcols(dom[j]).items():
        i = ridx.get(im)
        if i is not None:
            MS[(i, k)] = MS.get((i, k), 0) + val
A = matrix(QQ, n, len(S), MS, sparse=True)
emit("restricted matrix %d x %d, nnz=%d" % (n, len(S), len(MS)))
K = A.right_kernel()
emit("restricted nullity over QQ = %d" % K.dimension())
if K.dimension() == 0:
    emit("NO QQ solution on mod-p support; need support expansion")
else:
    v = K.basis()[0]
    terms = [(dom[S[k]], v[k]) for k in range(len(S)) if v[k] != 0]
    emit("candidate terms = %d" % len(terms))
    # clear denominators -> integral
    from sage.rings.rational import Rational
    dens = 1
    for _, c in terms:
        q = Rational(c).denominator()
        dens = dens * q // __import__("math").gcd(dens, q)
    inz = sorted((m, int(Rational(c) * dens)) for m, c in terms)
    emit("cleared denominator = %s" % dens)
    # verify D(F) = 0 exactly over QQ via integer arithmetic
    R = PolynomialRing(ZZ, "a0,a1,a2,a3,a4,a5")
    a = R.gens()
    F = sum(c * prod(a[i]**e for i, e in enumerate(m)) for m, c in inz)
    D = sum(a[i + 1] * a[i + 2] * F.derivative(a[i]) for i in range(4))
    emit("D(F) == 0 exactly: %s" % (D == 0))
    a0d = max(m[0] for m, _ in inz)
    emit("a0-degree = %d" % a0d)
    top = [(m, c) for m, c in inz if m[0] == a0d]
    emit("top-a0 terms:")
    for m, c in top:
        emit("  %s : %d" % (m, c))
    # p/q valuations of top coefficient (as poly in a1..a5)
    RB = PolynomialRing(ZZ, "a1,a2,a3,a4,a5")
    b = RB.gens()
    Ct = sum(c * prod(b[j]**m[j + 1] for j in range(5)) for m, c in top)
    emit("top coeff C = %s" % Ct)
    termsC = Ct.dict()
    vp = min(e[3] for e in termsC)
    vq = min(e[4] for e in termsC)
    emit("top nterms = %d" % len(termsC))
    emit("v_p(C) = %d (P-top needs >= %d)" % (vp, 2 * a0d))
    emit("v_q(C) = %d (Q-top-strong needs >= %d)" % (vq, 4 * ((a0d + 1) // 2)))
    with open("data/witness_w46.txt", "w") as fh:
        for m, c in inz:
            fh.write("%s %d\n" % (",".join(map(str, m)), c))

with open("data/witness_w46.log", "w") as fh:
    fh.write("\n".join(STS) + "\n")
