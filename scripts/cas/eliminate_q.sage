"""q-saturation elimination: E' = ker(k[p,Q,J1,J2,F0,H,T] -> A/qA), test == (S,p^2T-E,Q).
Map: p|->a4, Q|->0, J1|->2a1a4-a2^2, J2|->-a3^2, F0|->x^7/35, H|->Hbar_q,
T|->F46bar_true (= file/26460, TRUE scale so p^2T-E vanishes).
S_Q, E_Q with q->Q. Test both inclusions (exact Groebner).
Run: sage scripts/cas/eliminate_q.sage (stdout log)
"""
from fractions import Fraction
R = PolynomialRing(QQ, 'a0,a1,a2,a3,a4,p,Q,J1,J2,F0,H,T', order='lex')
a0, a1, a2, a3, a4, p, Q, J1, J2, F0, H, T = R.gens()
x = a3
F0b = x**7/35
# Hbar_q: HMONO terms with a5-exponent 0 (pure Sage, no sympy)
Hb = (630*a0*a3**7*a4**2 + 1225*a1**2*a3**6*a4**2
      - 1540*a1*a2**2*a3**6*a4 + 385*a2**4*a3**6)
print("Hbar_q terms:", len(Hb.dict()), flush=True)
F46t = R(0)
with open('data/witness_w46.txt') as fh:
    for line in fh:
        sp = line.strip().rsplit(' ', 1)
        e = tuple(map(int, sp[0].split(',')))
        if e[5] == 0:
            F46t += QQ(sp[1]) * a0**e[0]*a1**e[1]*a2**e[2]*a3**e[3]*a4**e[4]
F46t = F46t
print("F46bar terms:", len(F46t.dict()), flush=True)
print("F46bar nonzero:", F46t != 0, flush=True)
# NOTE (scale): witness file IS the normalization matching E_printed:
# p^2*Ffile - E == 0 exactly (verified). Do NOT rescale.
J = ideal([p - a4, Q, J1 - (2*a1*a4 - a2**2), J2 - (-x**2),
           F0 - F0b, H - Hb, T - F46t])
print("graph ideal built.", flush=True)
t = cputime()
G = J.groebner_basis()
print(f"GB done t={cputime()-t:.1f}s, size={len(G)}", flush=True)
keep = {str(p), str(Q), str(J1), str(J2), str(F0), str(H), str(T)}
E = [g for g in G if set(str(v) for v in g.variables()) <= keep]
print(f"elimination size: {len(E)}", flush=True)
S = Q**4*H - 11025*F0**2 - 105*Q**2*J2**5*J1 - 9*J2**7
Erel = (40000*Q**6*J1**7 + 193200*Q**4*J1**6*J2**2
        + 325164*Q**2*J1**5*J2**4 + 148225*J1**4*J2**6
        + 840*Q**2*J1**3*J2*H + 770*J1**2*J2**3*H + H**2)
I0 = ideal([S, p**2*T - Erel, Q])
print("S,C,Q in E:", (S in J), ((p**2*T - Erel) in J), (Q in J), flush=True)
t = cputime()
ok1 = all((g in I0) for g in E)
print(f"E subset (S,p2T-E,Q): {ok1} t={cputime()-t:.1f}s", flush=True)
ok2 = all((h in ideal(E)) for h in [S, p**2*T - Erel, Q])
print(f"(S,p2T-E,Q) subset E: {ok2}", flush=True)
print("EQUAL:", ok1 and ok2, flush=True)
