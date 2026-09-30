"""Axis 1 (fresh, correct): N=6 Fibonacci-weighted kernel probe in SageMath.
B = k[a1..a6], D(a1)=a2*a3, D(a2)=a3*a4, D(a3)=a4*a5, D(a4)=a5*a6, D(a5)=D(a6)=0.
Fibonacci weights wt = (8,5,3,2,1,1). D is weight-homogeneous of degree 0
(wt(a_n) = wt(a_{n+1})+wt(a_{n+2})), so ker is computed per-weight V_w -> V_w.
Compares against free ring on candidate weights (1,1,4,6,14).
Run: sage /tmp/opencode/n6_kernel_sage.py
"""
from sage.all import QQ, PolynomialRing, Matrix

WT = [8, 5, 3, 2, 1, 1]
GEN_WTS = [1, 1, 4, 6, 14]
W_MAX = 20

R = PolynomialRing(QQ, ['a1','a2','a3','a4','a5','a6'])
a1,a2,a3,a4,a5,a6 = R.gens()
VARS = [a1,a2,a3,a4,a5,a6]

def Dpoly(f):
    # derivation with D(a1)=a2a3, D(a2)=a3a4, D(a3)=a4a5, D(a4)=a5a6, D(a5)=D(a6)=0
    d = [a2*a3, a3*a4, a4*a5, a5*a6, R.zero(), R.zero()]
    out = R.zero()
    for i, v in enumerate(VARS):
        out += d[i] * f.derivative(v)
    return out

def wbasis(w):
    """exponent tuples of exact weight w."""
    out = []
    def rec(idx, left, cur):
        if idx == 6:
            if left == 0:
                out.append(tuple(cur))
            return
        v = WT[idx]
        for e in range(left // v + 1):
            rec(idx+1, left - v*e, cur+[e])
    rec(0, w, [])
    return out

def free_count(degs, w, memo={}):
    if w < 0:
        return 0
    if not degs:
        return 1 if w == 0 else 0
    key = (tuple(degs), w)
    if key in memo:
        return memo[key]
    first, rest = degs[0], degs[1:]
    s = sum(free_count(rest, w - first*e) for e in range(w//first + 1))
    memo[key] = s
    return s

def kernel_dim(w):
    basis = wbasis(w)
    n = len(basis)
    if n == 0:
        return 0, 0
    idx = {e: k for k, e in enumerate(basis)}
    # D maps V_w -> V_w; build matrix columns = coords of D(m)
    M = Matrix(QQ, n, n, sparse=True)
    for j, e in enumerate(basis):
        m = R.monomial(*e)
        dm = Dpoly(m)
        if dm.is_zero():
            continue
        for exp, c in dm.dict().items():
            i = idx.get(tuple(int(x) for x in exp))
            if i is not None:
                M[i, j] = c
    return n, n - M.rank()

print("w | dimV | kerdim | free(1,1,4,6,14) | gap")
gaps = []
for w in range(W_MAX+1):
    n, kd = kernel_dim(w)
    fc = free_count(GEN_WTS, w)
    gap = kd - fc
    if gap != 0:
        gaps.append((w, gap))
    print(f"{w:2d} | {n:4d} | {kd:3d} | {fc:3d} | {gap:+d}")

print("hidden/dependency gaps:", gaps or "none through w=%d" % W_MAX)

# ---- verify candidate generators ----
G1 = a5
G2 = a6
G3 = 2*a2*a5 - a3**2
G4 = 2*a3*a6 - a4**2
G5 = (105*a1*a5**2*a6**4 - 105*a2*a3*a4*a5*a6**3 + 35*a2*a4**3*a5*a6**2
      + 35*a3**2*a4**3*a6**2 - 21*a3*a4**5*a6 + 3*a4**7)
G = [G1,G2,G3,G4,G5]
print("D(Gi)==0:", [Dpoly(g).is_zero() for g in G])
J = Matrix([[g.derivative(v) for v in [a1,a2,a3,a5,a6]] for g in G])
print("jacobian minor det:", J.determinant().factor())
print("AXIS1 SAGE PROBE OK")
