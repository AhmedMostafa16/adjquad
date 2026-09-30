"""f13-chart certification WITHOUT rational gcd:
pi1(b) = NUM_b / f13^N, NUM_b = sum_i (-g13)^i D^i(b) f13^{N-i}/i!.
Since D(f13)=0: D(pi1)=D(NUM)/f13^N. Check D(NUM)==0 by expansion.
Then evaluate at collapse points via NUM(pt)/f13(pt)^N (no normalization)."""
import sys
sys.path.insert(0, "/projects/adjquad/scripts/cas")
from sympy import symbols, expand, Rational, diff, factorial
from check_s6 import HMONO, _mk

a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
A = [a0, a1, a2, a3, a4, a5]
DM = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}

def D5(f):
    return expand(sum(diff(f, v) * DM[v] for v in A))

x, y, z, p, q = a3, a2, a1, a4, a5
J1 = 2*p*z - y**2
J2 = 2*q*y - x**2
f13 = Rational(1, 35)*p*J2**3 + Rational(1, 4)*p*q**2*J1*J2
g13 = (a0*p**2*q**3 - Rational(1, 6)*a1*a3**3*p*q
       - Rational(19, 70)*a2**3*a3*q**2 + Rational(101, 420)*a2**2*a3**3*q
       - Rational(1, 35)*a2*a3**5)
H = expand(sum(co * _mk(e) for (co, e) in HMONO))

print("D(g13)-f13 =", expand(D5(g13) - f13) == 0)
print("D(f13) =", D5(f13) == 0)
print("=> D(s1)=1 by quotient rule, no rational arithmetic needed.")

orbits = {}
for b in A:
    orb = [expand(b)]
    while True:
        nxt = D5(orb[-1])
        if nxt == 0:
            break
        orb.append(nxt)
    orbits[b] = orb

import time
for b in [a3, a2, a1, a0]:
    t0 = time.time()
    orb = orbits[b]
    N = len(orb) - 1
    num = expand(sum(((-g13)**i) * orb[i] * (f13**(N - i)) / factorial(i)
                     for i in range(len(orb))))
    print(f"pi1({b}): N={N} numterms={len(num.args) if hasattr(num,'args') else 1} build={time.time()-t0:.1f}s")
    t0 = time.time()
    print(f"  D(NUM)==0: {D5(num) == 0} check={time.time()-t0:.1f}s")
    fd = Rational(-1, 35)
    for t in [0, 1, 2]:
        pt = {a0: 0, a1: Rational(t**2, 2), a2: t, a3: 1, a4: 1, a5: 0}
        print(f"  t={t}: pi1 = {num.subs(pt) / fd**N}")
