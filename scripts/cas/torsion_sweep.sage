"""Torsion discovery (CORRECTED): excess_r(w) = dim((C5:p^r)_w) - dim(C5_w)
over GF(1000003) (consistency/discovery; NOT a proof).
Correct formulation: M = C5-span matrix (rows A_{w+r} mons, cols gen-mons);
M' = M with p^r-divisible rows DELETED. c in ker(M') <=> sum c*g = p^r*a.
phi: ker(M') -> A_w, c |-> a; ker(phi) = ker(M).
dim feasible = nullity(M') - nullity(M); excess = dim feasible - rank(M_w).
Expect: r=1 -> 0; r=2 -> 1 at w=46 (F46), else 0; r=3 -> 0.
Run: sage scripts/cas/torsion_sweep.sage  (stdout log)
"""
from collections import defaultdict

ELL = 1000003
WT = (8, 5, 3, 2, 1, 1)
GW = (1, 1, 6, 4, 14, 24)  # p,q,J1,J2,F0,H

P = {(0, 0, 0, 0, 1, 0): 1}
Q = {(0, 0, 0, 0, 0, 1): 1}
J1 = {(0, 1, 0, 0, 1, 0): 2, (0, 0, 2, 0, 0, 0): ELL - 1}
J2 = {(0, 0, 1, 0, 0, 1): 2, (0, 0, 0, 2, 0, 0): ELL - 1}


def add(e1, e2):
    return (e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2],
            e1[3] + e2[3], e1[4] + e2[4], e1[5] + e2[5])


def pmul(A, B):
    R = defaultdict(int)
    for a, ca in A.items():
        for b, cb in B.items():
            R[add(a, b)] = (R[add(a, b)] + ca * cb) % ELL
    return dict(R)


def pscale(A, num, den):
    inv = pow(den, -1, ELL)
    return {k: (v * num * inv) % ELL for k, v in A.items()}


def ppow(A, n):
    R = {(0, 0, 0, 0, 0, 0): 1}
    for _ in range(n):
        R = pmul(R, A)
    return R


F0 = {(1, 0, 0, 0, 2, 4): 1, (0, 1, 1, 1, 1, 3): ELL - 1}
F0.update(pscale({(0, 1, 0, 3, 1, 2): 1}, 1, 3))
F0.update(pscale({(0, 0, 2, 3, 0, 2): 1}, 1, 3))
F0.update(pscale({(0, 0, 1, 5, 0, 1): ELL - 1}, 1, 5))
F0.update(pscale({(0, 0, 0, 7, 0, 0): 1}, 1, 35))
HMONO = [((11025), [2, 0, 0, 0, 4, 4]),
          ((-22050), [1, 1, 1, 1, 3, 3]),
          ((7350), [1, 1, 0, 3, 3, 2]),
          ((7350), [1, 0, 2, 3, 2, 2]),
          ((-4410), [1, 0, 1, 5, 2, 1]),
          ((630), [1, 0, 0, 7, 2, 0]),
          ((11025), [0, 2, 2, 2, 2, 2]),
          ((-7350), [0, 2, 1, 4, 2, 1]),
          ((1225), [0, 2, 0, 6, 2, 0]),
          ((6720), [0, 1, 5, 0, 1, 3]),
          ((-16800), [0, 1, 4, 2, 1, 2]),
          ((9450), [0, 1, 3, 4, 1, 1]),
          ((-1540), [0, 1, 2, 6, 1, 0]),
          ((-2208), [0, 0, 7, 0, 0, 3]),
          ((4368), [0, 0, 6, 2, 0, 2]),
          ((-2352), [0, 0, 5, 4, 0, 1]),
          ((385), [0, 0, 4, 6, 0, 0])]
H = {tuple(e): c % ELL for (c, e) in HMONO}
GENS = [P, Q, J1, J2, F0, H]


def gen_monomials(W):
    out = []

    def rec(i, rem, cur):
        if i == 5:
            if rem % GW[5] == 0:
                out.append(tuple(cur + [rem // GW[5]]))
            return
        for e in range(rem // GW[i] + 1):
            rec(i + 1, rem - e * GW[i], cur + [e])
    rec(0, W, [])
    return out


def expand_genmon(ge):
    R = {(0, 0, 0, 0, 0, 0): 1}
    for i, e in enumerate(ge):
        if e:
            R = pmul(R, ppow(GENS[i], e))
    return R


def amatrices(w, r):
    """Returns (Mprime, ngB, dimCW, dimCw).
    Mprime: C5-span cols restricted to p^r-FREE rows (small).
    Dims via the hypersurface Hilbert series s6(W)-s6(W-28) (exact:
    S is the full relation). nullF not computed (memory); consistency
    sweep only — exact nullities in torsion_exact.sage (QQ)."""
    W = w + r
    gmB = gen_monomials(W)

    def enum_A(WW):
        out = []

        def rec(rem, idx, cur):
            if idx == 6:
                if rem == 0:
                    out.append(tuple(cur))
                return
            for e in range(rem // WT[idx] + 1):
                rec(rem - e * WT[idx], idx + 1, cur + [e])
        rec(WW, 0, [])
        return out

    exB = [expand_genmon(ge) for ge in gmB]
    free = []
    seen = set()
    for E in exB:
        for m in E:
            if m[4] < r and m not in seen:
                seen.add(m)
                free.append(m)
    ifr = {m: i for i, m in enumerate(free)}
    Mp = Matrix(GF(ELL), len(free), len(gmB), sparse=True)
    for j, E in enumerate(exB):
        for m, c in E.items():
            if m in ifr:
                Mp[ifr[m], j] = c
    s6 = lambda WW: len(gen_monomials(WW))
    dimCW = s6(W) - (s6(W - 28) if W >= 28 else 0)
    dimCw = s6(w) - (s6(w - 28) if w >= 28 else 0)
    return Mp, len(gmB), dimCW, dimCw


for r in (1, 2, 3):
    for w in (40, 42, 44, 45, 46, 47, 48):
        t = cputime()
        Mp, ngB, dimCW, dimCw = amatrices(w, r)
        nP = Mp.ncols() - Mp.rank()
        print(f"r={r} w={w} Mprime={Mp.nrows()}x{Mp.ncols()} "
              f"nullP={nP} ngB={ngB} dimC5W={dimCW} dimC5w={dimCw} "
              f"excess={nP - (ngB - dimCW) - dimCw} t={cputime()-t:.1f}s",
              flush=True)
