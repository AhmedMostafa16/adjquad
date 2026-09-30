"""Residual p-boundary audit: delta_p on A/pA, theta, reductions, kernel dims.

A/pA = k[a0,a1,a2,a3,q] (p=a4=0); delta_p: a0->a1a2, a1->a2a3, rest 0.
theta = 2xa0-z^2 (x=a3,y=a2,z=a1). K-image: p->0, J1->-y^2, J2 unchanged.

Checks (PASS/FAIL each, final `residual OK`, exit 0/1):
  R1. delta_p actions on the five residue generators (exact expansion).
  R2. D(2a3a0-a1^2) = 2pqa0, i.e. theta is D-closed mod p (Thm 2A input).
  R3. Reductions: F0|p=0 = q^2x^3y^2/3-qx^5y/5+x^7/35; H|p=0 has 4 terms
      (a0-free); J1|p=0 = -y^2; J2|p=0 = J2; F46|p=0 != 0 (new residual
      invariant direction).
  R4. ker(delta_p) dims match k[q,x,y,theta] in total degree <= 8
      (bounded evidence for Thm thm:residual-kernel; the proof is in text).
  R5. F0r,Hr a0-free.
  R6. F46|p=0 = B*theta with B in k[q,x,y] explicit (Thm 2A normal form).

Run: python3 scripts/cas/check_residual.py  # log: data/residual.log
Lean counterpart: formalize/AdjQuad/ResidualCheck.lean
(`lake build AdjQuad.ResidualCheck`, zero sorry).
"""
import sys
from fractions import Fraction
from sympy import symbols, expand, Rational, diff

a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
A = [a0, a1, a2, a3, a4, a5]
x, y, z, p, q = a3, a2, a1, a4, a5
DM = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}
J1 = 2*p*z - y**2
J2 = 2*q*y - x**2
F0 = (p**2*q**4*a0 - p*q**3*x*y*z + Rational(1, 3)*p*q**2*x**3*z
      + Rational(1, 3)*q**2*x**3*y**2 - Rational(1, 5)*q*x**5*y
      + Rational(1, 35)*x**7)
TH = 2*x*a0 - z**2

sys.path.insert(0, "scripts/cas")
from check_s6 import HMONO, _mk  # noqa: E402

H = expand(sum(co * _mk(e) for (co, e) in HMONO))
F46 = 0
for line in open("data/witness_w46.txt"):
    sp = line.strip().rsplit(" ", 1)
    ex = tuple(map(int, sp[0].split(",")))
    F46 += Rational(sp[1]) * _mk(ex)
F46 = expand(F46)

fails = []


def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name +
          ((" [" + str(detail) + "]") if detail else ""))
    if not cond:
        fails.append(name)


def D5(f):
    return expand(sum(diff(f, v) * DM[v] for v in A))


sub0 = {p: 0}
check("R1 d(a0)=a1a2", D5(a0).subs(sub0) == a1*a2)
check("R1 d(a1)=a2a3", D5(a1).subs(sub0) == a2*a3)
check("R1 d(a2)=0", D5(a2).subs(sub0) == 0)
check("R1 d(a3)=0", D5(a3).subs(sub0) == 0)
check("R1 d(q)=0", D5(q).subs(sub0) == 0)
check("R2 D(theta)=2pqa0", expand(D5(TH) - 2*p*q*a0) == 0, D5(TH))
F0r = expand(F0.subs(sub0))
check("R3 F0|p=0 three terms",
      expand(F0r - (q**2*x**3*y**2/3 - q*x**5*y/5 + x**7/35)) == 0)
Hr = expand(H.subs(sub0))
from sympy import Poly as _P
HrM = _P(Hr, a0, a1, a2, a3, a5).monoms()
check("R3 H|p=0 a0-free", all(e[0] == 0 for e in HrM))
check("R3 H|p=0 four terms", len(HrM) == 4)
check("R3 J1|p=0=-y^2", expand(J1.subs(sub0) + y**2) == 0)
check("R3 J2|p=0=J2", expand(J2.subs(sub0) - J2) == 0)
F46r = expand(F46.subs(sub0))
check("R3 F46|p=0 != 0", F46r != 0)
F0rM = _P(F0r, a0, a1, a2, a3, a5).monoms()
check("R5 F0r,Hr a0-free",
      all(e[0] == 0 for e in F0rM)
      and all(e[0] == 0 for e in HrM))
# F46r carries a0: F46r = B*theta with B in k[q,x,y] (Thm 2A normal form)
TH = 2*x*a0 - z**2
_B = (235200*a2**9*a3**2*a5**5 + 1093680*a2**8*a3**4*a5**4
      - 1029420*a2**7*a3**6*a5**3 + 291060*a2**6*a3**8*a5**2
      - 26460*a2**5*a3**10*a5)
check("R6 F46|p=0 = B*theta", expand(F46r - _B*TH) == 0)


def mons4(n):
    if n < 0:
        return
    # monomials in (a0,a1,a2,a4)-> use (a0,a1,a2,a3,q) 5 vars total degree n
    def rec(rem, idx, cur):
        if idx == 5:
            if rem == 0:
                yield tuple(cur)
            return
        for e in range(rem + 1):
            yield from rec(rem - e, idx + 1, cur + [e])
    yield from rec(n, 0, [])


def dres(e):
    # delta_p on monomial (a0,a1,a2,a3,q) exps -> dict
    e0, e1, e2, e3, e4 = e
    res = {}
    if e0 > 0:  # d(a0)=a1a2
        m = (e0 - 1, e1 + 1, e2 + 1, e3, e4)
        res[m] = res.get(m, Fraction(0)) + e0
    if e1 > 0:  # d(a1)=a2a3
        m = (e0, e1 - 1, e2 + 1, e3 + 1, e4)
        res[m] = res.get(m, Fraction(0)) + e1
    return {k: v for k, v in res.items() if v != 0}


def rank(rows, ncols):
    M = [dict(r) for r in rows]
    pr = 0
    for col in range(ncols):
        p = None
        for r in range(pr, len(M)):
            if M[r].get(col, Fraction(0)) != 0:
                p = r
                break
        if p is None:
            continue
        M[pr], M[p] = M[p], M[pr]
        inv = M[pr][col]
        for k in list(M[pr]):
            M[pr][k] /= inv
        for r in range(len(M)):
            if r != pr and M[r].get(col, Fraction(0)) != 0:
                f = M[r][col]
                for k, v in M[pr].items():
                    M[r][k] = M[r].get(k, Fraction(0)) - f * v
                    if M[r][k] == 0:
                        del M[r][k]
        pr += 1
    return pr


def subdim(n):
    # k[q,x,y,theta]_n: q^a x^b y^c th^d, a+b+c+2d=n
    return sum(n - 2 * d + 2 - 1 + 1 - 1 for d in range(n // 2 + 1)
               for _ in [0] if False) or sum(
        (n - 2 * d + 2) * (n - 2 * d + 1) // 2 for d in range(n // 2 + 1))


r4 = True
for n in range(9):
    B = list(mons4(n))
    I = list(mons4(n + 1))
    jdx = {m: j for j, m in enumerate(I)}
    rows = [dict() for _ in I]
    for i, e in enumerate(B):
        for m, c in dres(e).items():
            rows[jdx[m]][i] = c
    kd = len(B) - rank(rows, len(B))
    if kd != subdim(n):
        r4 = False
        print(f"  deg {n}: ker={kd} subring={subdim(n)}")
check("R4 ker(delta_p)=k[q,x,y,th] deg<=8", r4)

if fails:
    print("residual FAILED:", fails)
    sys.exit(1)
print("residual OK")
