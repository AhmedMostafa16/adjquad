"""Exact QQ torsion certificates, low weights (fast, self-contained).

T1. (C5:p)_w = C5_w for 0<=w<=24 (excess_r via ker(M') formulation, exact).
T2. (C5:p^2)_w = C5_w for 0<=w<=24 (F46 at 46 is the first r=2 layer).
T3. V(q,x) terminal certs: descent identities, ker(delta) dims deg<=8,
    K-image forms, Kbar monomials never divisible by a1*a2.

Prints PASS/FAIL per check plus `torsion-qq OK` (exit 0/1).
Run: python3 scripts/cas/check_torsion_qq.py  # log: data/torsion_qq.log
"""
import sys
from fractions import Fraction

from sympy import symbols, expand, Rational, diff

a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
A = [a0, a1, a2, a3, a4, a5]
x, y, z, p, q = a3, a2, a1, a4, a5
DM = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}

WT = (8, 5, 3, 2, 1, 1)
GW = (1, 1, 6, 4, 14, 24)

J1 = {(0, 1, 0, 0, 1, 0): Fraction(2), (0, 0, 2, 0, 0, 0): Fraction(-1)}
J2 = {(0, 0, 1, 0, 0, 1): Fraction(2), (0, 0, 0, 2, 0, 0): Fraction(-1)}
F0 = {(1, 0, 0, 0, 2, 4): Fraction(1), (0, 1, 1, 1, 1, 3): Fraction(-1),
      (0, 1, 0, 3, 1, 2): Fraction(1, 3), (0, 0, 2, 3, 0, 2): Fraction(1, 3),
      (0, 0, 1, 5, 0, 1): Fraction(-1, 5), (0, 0, 0, 7, 0, 0): Fraction(1, 35)}
sys.path.insert(0, "scripts/cas")
from check_s6 import HMONO  # noqa: E402

H = {tuple(e): Fraction(c) for (c, e) in HMONO}
P = {(0, 0, 0, 0, 1, 0): Fraction(1)}
Q = {(0, 0, 0, 0, 0, 1): Fraction(1)}
GENS = [P, Q, J1, J2, F0, H]

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


def s6(W):
    return len(genmons(W))


def excess_qq(w, r):
    """excess_r(w) exactly: nullity(M') - (ng - dimC5(W)) - dimC5(w)."""
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
    dimCW = s6(W) - (s6(W - 28) if W >= 28 else 0)
    dimCw = s6(w) - (s6(w - 28) if w >= 28 else 0)
    return (nP - (len(gB) - dimCW)) - dimCw


t1 = all(excess_qq(w, 1) == 0 for w in range(0, 25))
check("T1 (C5:p)_w=C5_w w<=24 exact", t1)
t2 = all(excess_qq(w, 2) == 0 for w in range(0, 25))
check("T2 (C5:p^2)_w=C5_w w<=24 exact", t2)

# T3: terminal stratum
D5 = lambda f: expand(sum(diff(f, v) * DM[v] for v in A))  # noqa: E731
sJ1 = 2*p*z - y**2
sJ2 = 2*q*y - x**2
t3a = (D5(q) == 0 and expand(D5(x) - p*q) == 0
       and expand(sJ1.subs({q: 0, x: 0}) - (2*a4*a1 - a2**2)) == 0
       and expand(sJ2.subs({q: 0, x: 0})) == 0)


def smons(nv, deg):
    if nv == 1:
        yield (deg,)
        return
    for e0 in range(deg + 1):
        for rest in smons(nv - 1, deg - e0):
            yield (e0,) + rest


def strat_ker(n):
    basis = list(smons(4, n))
    img = list(smons(4, n + 1))
    jdx = {m: j for j, m in enumerate(img)}
    rows = [dict() for _ in img]
    for i, (e0, e1, e2, e3) in enumerate(basis):
        if e0 > 0:
            rows[jdx[(e0 - 1, e1 + 1, e2 + 1, e3)]][i] = Fraction(e0)
    M = [dict(r) for r in rows]
    piv = 0
    for col in range(len(basis)):
        p = None
        for r in range(piv, len(M)):
            if M[r].get(col, Fraction(0)) != 0:
                p = r
                break
        if p is None:
            continue
        M[piv], M[p] = M[p], M[piv]
        piv += 1
    return len(basis) - piv == (n + 2) * (n + 1) // 2


t3b = all(strat_ker(n) for n in range(9))
t3c = True
for cc in range(5):
    for aa in range(13 - 3 * cc):
        if aa + 3 * cc > 12:
            continue
        if expand((p**aa * (2*a4*a1 - a2**2)**cc).subs(a1, 0)) == 0:
            t3c = False
check("T3 terminal stratum V(q,x) certs", t3a and t3b and t3c)

if fails:
    print("torsion-qq FAILED:", fails)
    sys.exit(1)
print("torsion-qq OK")
