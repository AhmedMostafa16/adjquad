"""Discriminant of the cover P(T)-Z (exact, self-contained).
Recompute rho_j (s0-expansion), alpha, P_j = delta_{j1} - rho_j*(-alpha)^j
natively; clear denominators; Res_T; factor; report support.
Run: sage scripts/cas/cover_disc.sage
"""
B = PolynomialRing(QQ, 'p,q,Y,Z,s0')
p, q, Y, Z, s0 = B.gens()
# G0/c with x=pqs0, y=Y+p^2 q s0^2/2, z=Z+pqY s0^2/2+p^3q^2 s0^4/8, c=p^2q^4
X = p*q*s0
yy = Y + p**2*q*s0**2/2
zz = Z + p*q*Y*s0**2/2 + p**3*q**2*s0**4/8
G0 = (-p*q**3*X*yy*zz + p*q**2*X**3*zz/3 + q**2*X**3*yy**2/3
      - q*X**5*yy/5 + X**7/35)
c = p**2*q**4
G0j = [G0.coefficient({s0: j}) for j in range(8)]
print("rho degs:", [0 if g == 0 else 1 for g in G0j], flush=True)
print("rho_7 =", G0j[7]/c, flush=True)
assert G0j[7]/c == -p**5*q**3/112, "rho_7 mismatch"
for j in (0, 2, 4, 6):
    assert G0j[j] == 0, f"rho_{j} nonzero!"

R = PolynomialRing(QQ, 'p,q,J1,J2,Z,T')
p, q, J1, J2, Z, T = R.gens()
e2 = J2**2/35 + q**2*J1/4
f13 = p*J2**3/35 + p*q**2*J1*J2/4
alpha = p**2*q**3/f13
# map rho_j (in p,q,Y,Z) to base via Y=J2/(2q), Z=(J1+Y^2)/(2p)
B0 = PolynomialRing(QQ, 'p,q,Y,Z')
S = PolynomialRing(QQ, 'p,q,J1,J2')
FS = S.fraction_field()
sp, sq, sJ1, sJ2 = [FS(g) for g in S.gens()]
Yv = sJ2/(2*sq)
Zv = (sJ1 + (sJ2/(2*sq))**2)/(2*sp)


def subYZ(g):
    """Substitute Y_|->Yv, Z_|->Zv for g (dict may retain s0-slot at 0)."""
    out = FS(0)
    for e, c in g.dict().items():
        i, j, a, b = e[0], e[1], e[2], e[3]
        out += c * sp**i * sq**j * Yv**a * Zv**b
    return out


G0j = [subYZ(g) for g in G0j]
# lift to Rorden: coerce by variable name into R below
R = PolynomialRing(QQ, 'p,q,J1,J2,Z,T')
p, q, J1, J2, Z, T = R.gens()
G0j = [R(g.numerator())/R(g.denominator()) for g in G0j]
c = R(p)**2*R(q)**4
P = T - sum((G0j[j]/c) * (-alpha*T)**j for j in (1, 3, 5, 7))
P = R(P.numerator()) / R(P.denominator())
print("P built.", flush=True)
D1 = (35*J1*q**2 + 4*J2**2)
L = 3*J2**7*D1**7
Q = R((L*(P - Z)).numerator())
Qp = Q.derivative(T)
print("deg Q:", Q.degree(T), "deg Qp:", Qp.degree(T), flush=True)
t = cputime()
Res = Q.resultant(Qp, T)
print(f"resultant done t={cputime()-t:.1f}s, terms={len(Res.dict())}", flush=True)
print(Res.factor(), flush=True)
