"""Minimal primes of the p=0 fiber singular base (S, E, 2x2 minors).

Sing(X) cap V(p) = V(p, S, E, minors) x A^1_T since E has no p-term
(E|_{p=0} = E) and the relation p^2T-E vanishes identically on V(p).
Minimal primes here = fiber components (x A^1_T). Compare against the
old piece V(q,F0,J2,H) [old piece cap V(p)] to isolate NEW components.
Run: sage scripts/cas/sing_fiber.sage  (stdout log; primdec can be slow)
"""
R = PolynomialRing(QQ, 'q,J1,J2,F0,H')
q, J1, J2, F0, H = R.gens()
S = q**4*H - 11025*F0**2 - 105*q**2*J2**5*J1 - 9*J2**7
E = (40000*q**6*J1**7 + 193200*q**4*J1**6*J2**2 + 325164*q**2*J1**5*J2**4
     + 148225*J1**4*J2**6 + 840*q**2*J1**3*J2*H + 770*J1**2*J2**3*H + H**2)
rS = [S.derivative(v) for v in (q, J1, J2, F0, H)]
rE = [E.derivative(v) for v in (q, J1, J2, F0, H)]
mins = []
for i in range(5):
    for j in range(i+1, 5):
        m = rS[i]*rE[j] - rS[j]*rE[i]
        if m != 0:
            mins.append(m)
I = R.ideal([S, E] + mins)
print('dim base:', I.dimension(), flush=True)
t = cputime()
PD = I.primary_decomposition()
print('primdec t=%.1fs ncomps=%d' % (cputime() - t, len(PD)), flush=True)
for k, Q in enumerate(PD):
    print('--- component', k, 'dim', Q.dimension(), 'nprim' if False else '', flush=True)
    Rd = Q.radical()
    print('prime dim:', Rd.dimension(), flush=True)
    for g in Rd.gens():
        print('   ', g, flush=True)
