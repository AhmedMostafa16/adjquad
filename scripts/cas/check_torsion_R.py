"""Torsion of R=C5[F46]: excess_r^R(w) = dim((R:p^r)_w) - dim(R_w), exact QQ.
R-span members: gen-monomials in (p,q,J1,J2,F0,H,F46); image-span method
(relations automatic). F46 loaded from data/witness_w46.txt (scale-free).
M'-formulation: nullity(M') - (ng - dimRW) - dimRw, with dimRW/dimRw from
spans (no Hilbert assumption on R).
Expect: all 0 (R kills the C5-torsion; new nonzero = torsion falsifier).
Prints PASS/FAIL per (r,w) plus `torsion-R OK` (exit 0/1).
Run: python3 scripts/cas/check_torsion_R.py  # log: data/torsion_R.log
"""
import sys
from fractions import Fraction

WT = (8, 5, 3, 2, 1, 1)
GW = (1, 1, 6, 4, 14, 24, 46)

J1 = {(0, 1, 0, 0, 1, 0): Fraction(2), (0, 0, 2, 0, 0, 0): Fraction(-1)}
J2 = {(0, 0, 1, 0, 0, 1): Fraction(2), (0, 0, 0, 2, 0, 0): Fraction(-1)}
F0 = {(1, 0, 0, 0, 2, 4): Fraction(1), (0, 1, 1, 1, 1, 3): Fraction(-1),
      (0, 1, 0, 3, 1, 2): Fraction(1, 3), (0, 0, 2, 3, 0, 2): Fraction(1, 3),
      (0, 0, 1, 5, 0, 1): Fraction(-1, 5), (0, 0, 0, 7, 0, 0): Fraction(1, 35)}
sys.path.insert(0, "scripts/cas")
from check_s6 import HMONO  # noqa: E402

H = {tuple(e): Fraction(c) for (c, e) in HMONO}
F46 = {}
with open("data/witness_w46.txt") as fh:
    for line in fh:
        sp = line.strip().split()
        F46[tuple(map(int, sp[0].split(",")))] = Fraction(sp[1])
P = {(0, 0, 0, 0, 1, 0): Fraction(1)}
Q = {(0, 0, 0, 0, 0, 1): Fraction(1)}
GENS = [P, Q, J1, J2, F0, H, F46]

fails = []


def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name +
          ((" [" + str(detail) + "]") if detail else ""))
    if not cond:
        fails.append(name)


def add(e1, e2):
    return tuple(a + b for a, b in zip(e1, e2))


def pmul(A, B):
    R = {}
    for a, ca in A.items():
        for b, cb in B.items():
            k = add(a, b)
            R[k] = R.get(k, Fraction(0)) + ca * cb
    return {k: v for k, v in R.items() if v != 0}


def ppow(A, n):
    R = {(0, 0, 0, 0, 0, 0): Fraction(1)}
    for _ in range(n):
        R = pmul(R, A)
    return R


def genmons(W):
    # 7 generators (p,q,J1,J2,F0,H,F46); F46^2 (wt 92) never needed here.
    out = []

    def rec(i, rem, cur):
        if i == 6:
            if rem == 0:
                out.append(tuple(cur + [0]))
            elif rem == 46:
                out.append(tuple(cur + [1]))
            return
        for e in range(rem // GW[i] + 1):
            rec(i + 1, rem - e * GW[i], cur + [e])
    rec(0, W, [])
    return out


def expge(ge):
    R = {(0, 0, 0, 0, 0, 0): Fraction(1)}
    for i, e in enumerate(ge):
        if e:
            R = pmul(R, ppow(GENS[i], e))
    return R


def nullity(rows, ncols):
    M = [dict(r) for r in rows]
    piv = 0
    for col in range(ncols):
        p = None
        for r in range(piv, len(M)):
            if M[r].get(col, Fraction(0)) != 0:
                p = r
                break
        if p is None:
            continue
        M[piv], M[p] = M[p], M[piv]
        inv = M[piv][col]
        for k in list(M[piv]):
            M[piv][k] /= inv
        for r in range(len(M)):
            if r != piv and M[r].get(col, Fraction(0)) != 0:
                f = M[r][col]
                for k, v in M[piv].items():
                    M[r][k] = M[r].get(k, Fraction(0)) - f * v
                    if M[r][k] == 0:
                        del M[r][k]
        piv += 1
    return ncols - piv


def excess_R(w, r):
    W = w + r
    gB = genmons(W)
    exB = [expge(ge) for ge in gB]
    free = []
    seen = set()
    for E in exB:
        for m in E:
            if m[4] < r and m not in seen:
                seen.add(m)
                free.append(m)
    fr = {m: i for i, m in enumerate(free)}
    Mp = [dict() for _ in range(len(free))]
    for j, E in enumerate(exB):
        for m, c in E.items():
            if m in fr:
                Mp[fr[m]][j] = c
    nP = nullity(Mp, len(gB))
    # dim R_W, dim R_w via image spans (need full row sets)
    allm = set()
    for E in exB:
        allm.update(E)
    allm = sorted(allm)
    ia = {m: i for i, m in enumerate(allm)}
    Mf = [dict() for _ in range(len(allm))]
    for j, E in enumerate(exB):
        for m, c in E.items():
            Mf[ia[m]][j] = c
    dimRW = len(gB) - nullity(Mf, len(gB))
    gs = genmons(w)
    exs = [expge(ge) for ge in gs]
    alls = sorted({m for E in exs for m in E})
    ias = {m: i for i, m in enumerate(alls)}
    Mw = [dict() for _ in range(len(alls))]
    for j, E in enumerate(exs):
        for m, c in E.items():
            Mw[ias[m]][j] = c
    dimRw = len(gs) - nullity(Mw, len(gs))
    return (nP - (len(gB) - dimRW)) - dimRw, len(free), len(gB)


for r, w in ([(1, w) for w in range(0, 53)] + [(2, w) for w in range(0, 51)]):
    ex, nr, nc = excess_R(w, r)
    check(f"R r={r} w={w} excess={ex} (M'{nr}x{nc})", ex == 0)

if fails:
    print("torsion-R FAILED:", fails)
    sys.exit(1)
print("torsion-R OK")
