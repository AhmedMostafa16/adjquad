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
        if m != 0: mins.append(m)
print('nonzero minors:', len(mins), flush=True)
I = R.ideal([S, E] + mins)
t = cputime()
print('dim Sing-section:', I.dimension(), flush=True)
print('dim t=%.1fs' % (cputime()-t), flush=True)
t = cputime()
Rd = I.radical()
print('radical t=%.1fs' % (cputime()-t), flush=True)
print(Rd, flush=True)
