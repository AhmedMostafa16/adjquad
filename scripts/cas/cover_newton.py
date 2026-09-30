"""Corrected Newton data: substitute Y_,Z_ back to (p,q,J1,J2), factor, read valuations.
Y_ = J2/(2q); Z_ = (J1+Y_^2)/(2p). Work in UFD k[p,q,J1,J2].
"""
from sympy import symbols, expand, Rational, Poly, factor

a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
x, y, z, p, q = a3, a2, a1, a4, a5
s0 = symbols('s0')
Y_, Z_ = symbols('Y_ Z_')
J1 = 2*p*z - y**2
J2 = 2*q*y - x**2
F0 = (p**2*q**4*a0 - p*q**3*x*y*z + Rational(1, 3)*p*q**2*x**3*z
      + Rational(1, 3)*q**2*x**3*y**2 - Rational(1, 5)*q*x**5*y
      + Rational(1, 35)*x**7)
c = p**2*q**4
G0 = expand(F0 - c*a0)
rho = G0/c
f13 = Rational(1, 35)*p*J2**3 + Rational(1, 4)*p*q**2*J1*J2
alpha = p**2*q**3/f13

X = p*q*s0
yy = Y_ + p**2*q*s0**2/2
zz = Z_ + p*q*Y_*s0**2/2 + p**3*q**2*s0**4/8
rhos = expand(rho.subs(x, X).subs(y, yy).subs(z, zz))
P = Poly(rhos, s0)
rhoj = [expand(P.nth(j)) for j in range(8)]

# back-substitution to (p,q,J1,J2)
J1s, J2s = symbols('J1s J2s')
f13a = p*J2s**3/35 + p*q**2*J1s*J2s/4
alpha = p**2*q**3/f13a
Yb = J2s/(2*q)
Zb = (J1s + Yb**2)/(2*p)


def tobase(expr):
    e = expand(expr.subs(Y_, Yb).subs(Z_, Zb))
    e = expand(e.subs(z, (J1s + 2*q*y - x**2) * 0 + 0))  # no-op safeguard
    return e


PJ = {}
for j in range(8):
    raw = (1 if j == 1 else 0) - rhoj[j] * (-alpha)**j
    PJ[j] = tobase(raw)


def val(expr, var):
    from sympy import fraction, together
    n, d = fraction(together(expr))
    vn, vd = 0, 0
    Pn, Pd = Poly(n, var), Poly(d, var)
    while Pn is not None and not Pn.is_zero and Pn.eval(0) == 0:
        qq, rr = Pn.div(Poly(var, var))
        if not rr.is_zero:
            break
        vn += 1
        Pn = qq
    while Pd is not None and not Pd.is_zero and Pd.eval(0) == 0:
        qq, rr = Pd.div(Poly(var, var))
        if not rr.is_zero:
            break
        vd += 1
        Pd = qq
    return vn - vd


print("j : iszero | vq | vp", flush=True)
for j in range(8):
    isz = expand(PJ[j]) == 0
    if isz:
        print(f"{j} : ZERO", flush=True)
    else:
        print(f"{j} : vq={val(PJ[j], q)} vp={val(PJ[j], p)}", flush=True)
# factor the nonzero odd ones to display shape
for j in (1, 3, 5, 7):
    if expand(PJ[j]) != 0:
        print(f"P_{j} factored:", factor(PJ[j]), flush=True)

# v_q(Z): Z = NUM/f13^7 with NUM the a0-projection numerator (456 terms)
from sympy import diff, factorial as _fact
_A = [a0, a1, a2, a3, a4, a5]
DM0 = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}


def _D(f):
    return expand(sum(diff(f, v) * DM0[v] for v in _A))


_orb = [a0]
while True:
    _nxt = _D(_orb[-1])
    if expand(_nxt) == 0:
        break
    _orb.append(_nxt)
_f13 = Rational(1, 35)*p*(2*q*y - x**2)**3 + Rational(1, 4)*p*q**2*(2*p*z - y**2)*(2*q*y - x**2)
_g13 = (a0*p**2*q**3 - Rational(1, 6)*a1*a3**3*p*q
        - Rational(19, 70)*a2**3*a3*q**2 + Rational(101, 420)*a2**2*a3**3*q
        - Rational(1, 35)*a2*a3**5)
_NUM = sum(((-_g13)**i) * _orb[i] * (_f13**(7 - i))/_fact(i)
           for i in range(len(_orb)))
print("v_q(Z)=v_q(NUM):", expand(_NUM).subs(q, 0) != 0, flush=True)
