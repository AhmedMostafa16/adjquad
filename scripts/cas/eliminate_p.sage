"""Elimination ideal E = ker(k[q,J1,J2,F0,H] -> k[q,x,y]) and test E == (S, cbar46).
Map: q|->q, J1|->-y^2, J2|->2qy-x^2, F0|->F0bar, H|->Hbar (all mod-p forms).
S = q^4*H-11025*F0^2-105*q^2*J2^5*J1-9*J2^7 (p-free, so Sbar = S).
cbar46 = 40000q^6J1^7+193200q^4J1^6J2^2+325164q^2J1^5J2^4+148225J1^4J2^6
         +840q^2J1^3J2H+770J1^2J2^3H+H^2 (p^2F46 relation mod p).
Run: sage scripts/cas/eliminate_p.sage (stdout log)
"""
R = PolynomialRing(QQ, 'x,y,q,J1,J2,F0,H', order='lex')
x, y, q, J1, J2, F0, H = R.gens()
F0b = q**2*x**3*y**2/3 - q*x**5*y/5 + x**7/35
Hb = (-2208*y**7*q**3 + 4368*y**6*x**2*q**2 - 2352*y**5*x**4*q
      + 385*y**4*x**6)
J = ideal([J1 + y**2, J2 - (2*q*y - x**2), F0 - F0b, H - Hb])
print("graph ideal built.", flush=True)
t = cputime()
G = J.groebner_basis()
print(f"GB done t={cputime()-t:.1f}s, size={len(G)}", flush=True)
E = [g for g in G if set(str(v) for v in g.variables()) <=
     {str(q), str(J1), str(J2), str(F0), str(H)}]
print(f"elimination basis size: {len(E)}", flush=True)
for g in E:
    print("  E-gen:", g, flush=True)
S = q**4*H - 11025*F0**2 - 105*q**2*J2**5*J1 - 9*J2**7
C = (40000*q**6*J1**7 + 193200*q**4*J1**6*J2**2 + 325164*q**2*J1**5*J2**4
     + 148225*J1**4*J2**6 + 840*q**2*J1**3*J2*H + 770*J1**2*J2**3*H + H**2)
I0 = ideal([S, C])
print("S in E:", S in J, flush=True)
print("C in E:", C in J, flush=True)
t = cputime()
IE = ideal(E)
ok1 = all((g in I0) for g in E)
print(f"E subset (S,C): {ok1} t={cputime()-t:.1f}s", flush=True)
ok2 = (S in IE) and (C in IE)
print(f"(S,C) subset E: {ok2}", flush=True)
print("EQUAL:", ok1 and ok2, flush=True)
