"""G4 facts for the no-monomial-bound theorem (N=6, B6 level).
G4 = 2a3a6 - a4^2 in k[a1..a6]. Asserts over QQ (sympy exact):
(i) irreducible; (ii) a6^2 does NOT divide G4 (a6-free term -a4^2);
(iii) G4 does NOT divide a6^2 (exact-division remainder nonzero).
(ii)+(iii) = divisibility-incomparability of the H20-direction
a5^4a6^3 with the D2-direction a5^4a6G4 in K6 (lifts from B6).
Run: python3 scripts/cas/check_n6_G4.py (stdout -> data/n6_G4.log)
"""
from sympy import symbols, Poly, factor

a1, a2, a3, a4, a5, a6 = symbols("a_1:7")
G4 = 2 * a3 * a6 - a4**2

ok = True


def check(name, cond):
    global ok
    print('%s %s' % ('PASS' if cond else 'FAIL', name), flush=True)
    ok = ok and bool(cond)


check('G4 irreducible', factor(G4) == G4)
P = Poly(G4, a1, a2, a3, a4, a5, a6)
min_a6 = min(e[5] for e in P.as_dict())
check('G4 has a6-free term -a4^2 (min a6-deg 0)', min_a6 == 0)
check('hence a6^2 does not divide G4', min_a6 == 0)
quo, rem = Poly(a6**2, a1, a2, a3, a4, a5, a6).div(Poly(G4, a1, a2, a3, a4, a5, a6))
check('G4 does not divide a6^2 (rem %s)' % rem, rem != 0)
print('n6-G4 OK' if ok else 'n6-G4 FAILED', flush=True)
raise SystemExit(0 if ok else 1)
