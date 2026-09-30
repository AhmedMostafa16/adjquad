"""Plinth-membership audit for D5 (referee assessment verification).

Proves by exact rational arithmetic (SymPy):
  P1. D5(pq) = 0; D5(px) = p^2*q != 0; D5(xy) = p*q*y + p*x^2 != 0,
      i.e. pq is invariant (hence in the plinth) while px, xy lie in
      the image but are not invariant (Lemma lem:plinth).
  P2. c = p^2*q^4 = D5(a3*a4*a5^3), i.e. the pole denominator lies in
      the image, hence in pl(D5).
  P3. f13 = p*J2^3/35 + p*q^2*J1*J2/4 satisfies D5(g13) = f13 for the
      five-term g13, D5(f13) = 0, and f13|_{q=0} = -p*x^6/35 != 0,
      i.e. a q-primitive plinth element: pl(D5) != (pq)K
      (Theorem thm:f13). Transition: with s0 = x/(pq), s1 = g13/f13,
      s1 - s0 = F0/(q*f13) (Theorem thm:second-chart).
  S1. D2^2 = 0 on generators but D2^2(a0^2) = 2*(a1*a2)^2 != 0,
      i.e. exp/D2-automorphism agreement holds on generators while the
      operator identity exp = 1 + lD2 is false (Prop. defect sharpness).

Lean counterpart (kernel-checked): formalize/AdjQuad/PlinthCheck.lean
(`lake build AdjQuad.PlinthCheck`, zero sorry).

Run: python3 scripts/cas/check_plinth.py  # log: data/plinth.log
Prints PASS/FAIL per check plus a final `plinth OK` on success
(`plinth FAILED` otherwise; exit 0/1).
"""
import sys
from sympy import symbols, expand, diff, Rational, cancel

a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
x, y, z, p, q = a3, a2, a1, a4, a5

fails = []


def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name +
          ((" [" + str(detail) + "]") if detail else ""))
    if not cond:
        fails.append(name)


def D5(f):
    d = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}
    return expand(sum(diff(f, v) * d[v] for v in d))


check("D5(pq)=0", D5(p*q) == 0)
check("D5(px)=p^2q", D5(p*x) == p**2*q, D5(p*x))
check("px not invariant", D5(p*x) != 0)
check("D5(xy)=pqy+px^2", D5(x*y) == p*q*y + p*x**2, D5(x*y))
check("xy not invariant", D5(x*y) != 0)
c = p**2 * q**4
check("c=D5(a3a4a5^3)", expand(D5(a3*a4*a5**3) - c) == 0)

J1 = 2*p*z - y**2
J2 = 2*q*y - x**2
f13 = Rational(1, 35)*p*J2**3 + Rational(1, 4)*p*q**2*J1*J2
g13 = (a0*p**2*q**3 - Rational(1, 6)*a1*a3**3*p*q
       - Rational(19, 70)*a2**3*a3*q**2 + Rational(101, 420)*a2**2*a3**3*q
       - Rational(1, 35)*a2*a3**5)
check("D5(f13)=0", D5(f13) == 0)
check("D5(g13)=f13", expand(D5(g13) - f13) == 0)
check("f13|q=0=-px^6/35!=0",
      expand(f13.subs(q, 0) + p*x**6/35) == 0 and f13.subs(q, 0) != 0,
      f13.subs(q, 0))
F0 = (p**2*q**4*a0 - p*q**3*x*y*z + Rational(1, 3)*p*q**2*x**3*z
      + Rational(1, 3)*q**2*x**3*y**2 - Rational(1, 5)*q*x**5*y
      + Rational(1, 35)*x**7)
s0 = x/(p*q)
s1 = g13/f13
check("s1-s0=F0/(q f13)", cancel(s1 - s0 - F0/(q*f13)) == 0)

b0, b1, b2 = symbols('b0 b1 b2')


def D2(f):
    d = {b0: b1*b2, b1: 0, b2: 0}
    return expand(sum(diff(f, v) * d[v] for v in d))


check("D2^2=0 on generators",
      D2(D2(b0)) == 0 and D2(D2(b1)) == 0 and D2(D2(b2)) == 0)
r = D2(D2(b0**2))
check("D2^2(a0^2)=2(a1a2)^2!=0", r == 2*(b1*b2)**2 and r != 0, r)

if fails:
    print("plinth FAILED:", fails)
    sys.exit(1)
print("plinth OK")
