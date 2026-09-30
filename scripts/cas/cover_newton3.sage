"""Divisorial cover data: Newton polygons of P(T)-Z at q, J2, e2 (exact),
and the 7x7 change-of-basis matrix (Z^j reduced mod P(W)-Z) + det + support.
P(T) rebuilt natively (rho s0-expansion). All exact over QQ.
Run: sage scripts/cas/cover_newton3.sage (stdout log)
"""
# ---------- rebuild P ----------
B = PolynomialRing(QQ, 'p,q,Y,Zz,s0')
p, q, Y, Zz, s0 = B.gens()
X = p*q*s0
yy = Y + p**2*q*s0**2/2
zz = Zz + p*q*Y*s0**2/2 + p**3*q**2*s0**4/8
G0 = (-p*q**3*X*yy*zz + p*q**2*X**3*zz/3 + q**2*X**3*yy**2/3
      - q*X**5*yy/5 + X**7/35)
c = p**2*q**4
G0j = [G0.coefficient({s0: j}) for j in range(8)]
assert all(G0j[j] == 0 for j in (0, 2, 4, 6)), "rho even nonzero"
assert G0j[7]/c == -p**5*q**3/112, "rho7 mismatch"
S = PolynomialRing(QQ, 'p,q,J1,J2')
FS = S.fraction_field()
sp, sq, sJ1, sJ2 = [FS(g) for g in S.gens()]
Yv = sJ2/(2*sq)
Zv = (sJ1 + (sJ2/(2*sq))**2)/(2*sp)


def subYZ(g):
    out = FS(0)
    for e, cval in g.dict().items():
        i, j, a, b = e[0], e[1], e[2], e[3]
        out += cval * sp**i * sq**j * Yv**a * Zv**b
    return out


G0s = [subYZ(g) for g in G0j]
K = S.fraction_field()
kp, kq, kJ1, kJ2 = [K(g) for g in S.gens()]
alpha = kp**2*kq**3/(kp*kJ2**3/35 + kp*kq**2*kJ1*kJ2/4)
# P_j = delta_{j1} - (G0j[j]/c)*(-alpha)^j  (j odd only nonzero)
PJ = {}
for j in (1, 3, 5, 7):
    PJ[j] = ((1 if j == 1 else 0) - (G0s[j]/(kp**2*kq**4)) * (-alpha)**j)
print("P rebuilt.", flush=True)


def vprime(F, prime):
    """valuation of F in Frac(S) along irreducible prime (in S)."""
    n = S(F.numerator())
    d = S(F.denominator())
    v = 0
    while True:
        q0, r0 = n.quo_rem(prime)
        if r0 != 0:
            break
        v += 1
        n = q0
    while True:
        q0, r0 = d.quo_rem(prime)
        if r0 != 0:
            break
        v -= 1
        d = q0
    return v


qP = S(q)
J2P = S(J2 if False else S.gens()[3])
e2P = sJ2**2/35 + sq**2*sJ1/4
e2P = S(e2P.numerator())
print("primes: q, J2, e2 =", qP, J2P, e2P, flush=True)
print("e2 factors:", e2P.factor(), flush=True)
for name, pr in (("q", qP), ("J2", J2P), ("e2", e2P)):
    pts = [(1, 0)] + [(j, vprime(PJ[j], pr)) for j in (1, 3, 5, 7)]
    # PJ[1] has constant term 1; report its valuation too
    print(f"prime {name}: points {pts}", flush=True)
    # lower hull from (0,0) [Z generic unit] -- report segments
    pts0 = [(0, 0)] + pts[1:]
    hull = [(0, 0)]
    while hull[-1][0] < 7:
        x0, y0 = hull[-1]
        best = None
        for (x1, y1) in pts0:
            if x1 <= x0:
                continue
            s = (y1 - y0)/(x1 - x0)
            if best is None or s < best[0] - 1e-12 or \
               (abs(s - best[0]) < 1e-12 and x1 > best[1]):
                best = (s, x1, y1)
        hull.append((best[1], best[2]))
    print(f"  hull: {hull}", flush=True)

# ---------- note on the 7x7 change-of-basis matrix (DEGENERATE, not computed) ----------
# Reducing Z^j mod (P(W)-Z) is trivial: Z^j lies in the coefficient field
# K(Z), so every remainder is (Z^j,0,...,0) and any such matrix has det 0
# (confirmed mod 1000003: det == 0). The finite lattice data are the Newton
# polygons above and the discriminant (cover_disc.sage), not this matrix.
