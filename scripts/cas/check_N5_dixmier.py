"""Dixmier ledger certificate for the N=5 O1-analog (supports the proof).

B5 = k[a1..a5], local slice s = a3/(a4a5) (D5(s) = 1 on B_{pq}),
Y = J2/(2q), Z = (J1+Y^2)/(2p). With a1a2 = sum_k e_k s^k:
  e_0 = (4Q^2UV+V^3)/(16PQ^3), e_2 = (4PQ^2U+3PV^2)/(16Q),
  e_4 = 3P^3QV/16, e_6 = P^5Q^3/16 (odd vanish),
and the fixed integrator T = sum_k e_k s^{k+1}/(k+1) has, over
Frac(k[a1,a2,a4,a5])[x] (x = a3):
  x^7: -1/(p^2q^4), x^5: a2/(p^2q^3),
  x^3: -(a1a4^2a5^2+a2^2a4a5^2)/(p^3q^4), x^1: a1a2/(pq),
odd-only. Every solution (mu, nu) of a1a2*mu + D5(nu) = 0 satisfies
nu = N_0 - mu*T (N_0 in R_{pq} free); validated end-to-end on (c, +G0).

Run:
    python3 scripts/cas/check_N5_dixmier.py  # log: data/n5_dixmier.log
Prints PASS/FAIL per check plus a final `check_N5_dixmier OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

_SYM = {}


def _sym():
    if not _SYM:
        from sympy import symbols
        a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
        P, Q, U, V, s, x = symbols("P Q U V s x")
        _SYM.update(a0=a0, a1=a1, a2=a2, a3=a3, a4=a4, a5=a5,
                    P=P, Q=Q, U=U, V=V, s=s, x=x)
    return _SYM


def _forms():
    from sympy import Rational
    s = _sym()
    P, Q, U, V, ss = s["P"], s["Q"], s["U"], s["V"], s["s"]
    Yv = V/(2*Q)
    Zv = (U + Yv**2)/(2*P)
    y_form = Yv + Rational(1, 2)*P**2*Q*ss**2
    z_form = (Zv + Rational(1, 2)*P*Q*Yv*ss**2
              + Rational(1, 8)*P**3*Q**2*ss**4)
    return y_form, z_form


def e_coeffs():
    """{k: e_k} s-coefficients of a1a2 in R-symbols (P,Q,U,V,s)."""
    from sympy import Poly, expand
    s = _sym()
    y_form, z_form = _forms()
    a1a2 = expand(z_form * y_form)
    return {mon[0]: cf for mon, cf in Poly(a1a2, s["s"]).as_dict().items()}


def x_coeffs():
    """{xpow: (num, (dp, dq))} x-basis of T over Frac(k[a1,a2,a4,a5])."""
    from sympy import Poly, expand
    s = _sym()
    e = e_coeffs()
    T = sum(cf * s["s"]**(k+1)/(k+1) for k, cf in e.items())
    Tred = expand(T.subs({s["U"]: 2*s["a1"]*s["a4"] - s["a2"]**2,
                          s["V"]: 2*s["a2"]*s["a5"] - s["x"]**2,
                          s["P"]: s["a4"], s["Q"]: s["a5"],
                          s["s"]: s["x"]/(s["a4"]*s["a5"])}))
    out = {}
    for mon, cf in Poly(Tred, s["x"]).as_dict().items():
        num, den = expand(cf).as_numer_denom()
        dp = Poly(den, s["a4"]).degree() if den.has(s["a4"]) else 0
        dq = Poly(den, s["a5"]).degree() if den.has(s["a5"]) else 0
        out[mon[0]] = (num, (dp, dq))
    return out


log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def main():
    from sympy import Rational, expand, Poly
    ok = True
    s = _sym()
    P, Q, U, V, ss = s["P"], s["Q"], s["U"], s["V"], s["s"]
    a1, a2, a3, a4, a5 = s["a1"], s["a2"], s["a3"], s["a4"], s["a5"]
    y_form, z_form = _forms()
    # 1. Reconstruction recovers a1,a2,a3 (premise of the s-basis).
    ok &= check("x recovers a3", expand(P*Q*ss).subs(
        {P: a4, Q: a5, ss: a3/(a4*a5)}) == a3)
    ok &= check("y recovers a2", expand(y_form.subs(
        {U: 2*a1*a4 - a2**2, V: 2*a2*a5 - a3**2, P: a4, Q: a5,
         ss: a3/(a4*a5)})) == a2)
    ok &= check("z recovers a1", expand(z_form.subs(
        {U: 2*a1*a4 - a2**2, V: 2*a2*a5 - a3**2, P: a4, Q: a5,
         ss: a3/(a4*a5)})) == a1)
    # 2. s-support of a1a2 and exact e_k.
    e = e_coeffs()
    ok &= check("s-support of a1a2 is [0,2,4,6]", sorted(e) == [0, 2, 4, 6])
    ok &= check("e_0 exact",
                expand(e[0] - (4*Q**2*U*V + V**3)/(16*P*Q**3)) == 0)
    ok &= check("e_2 exact",
                expand(e[2] - (4*P*Q**2*U + 3*P*V**2)/(16*Q)) == 0)
    ok &= check("e_4 exact", expand(e[4] - 3*P**3*Q*V/16) == 0)
    ok &= check("e_6 exact", expand(e[6] - P**5*Q**3/16) == 0)
    # 3. x-basis of T: support, denominators, full numerators.
    d = x_coeffs()
    ok &= check("x-support of T is [1,3,5,7]", sorted(d) == [1, 3, 5, 7])
    ok &= check("x^7 = -1/(p^2q^4)",
                d[7][1] == (2, 4) and expand(d[7][0] + 1) == 0)
    ok &= check("x^5 = a2/(p^2q^3)",
                d[5][1] == (2, 3) and expand(d[5][0] - a2) == 0)
    ok &= check("x^3 num exact",
                d[3][1] == (3, 4) and expand(
                    d[3][0] + (a1*a4**2*a5**2 + a2**2*a4*a5**2)) == 0)
    ok &= check("x^1 = a1a2/(pq)",
                d[1][1] == (1, 1) and expand(d[1][0] - a1*a2) == 0)
    # 4. End-to-end: N_{k+1} = -c*e_k/(k+1) reproduces +G0 (c = P^2Q^4).
    p, q = a4, a5
    G0 = (-p*q**3*a3*a2*a1 + Rational(1, 3)*p*q**2*a3**3*a1
          + Rational(1, 3)*q**2*a3**3*a2**2 - Rational(1, 5)*q*a3**5*a2
          + Rational(1, 35)*a3**7)
    G0s = expand(G0.subs({a1: z_form, a2: y_form, a3: P*Q*ss, a4: P,
                           a5: Q}))
    g = {mon[0]: cf for mon, cf in Poly(G0s, ss).as_dict().items()}
    c = P**2 * Q**4
    allmatch = True
    for k in range(8):
        if expand(-c * e.get(k, 0)/(k+1) - g.get(k+1, 0)) != 0:
            allmatch = False
    ok &= check("N-formulas reproduce +G0 (k=0..7)", allmatch)
    ok &= check("N_0 of +G0 is 0", expand(g.get(0, 0)) == 0)
    for ln in log:
        print(ln)
    print("check_N5_dixmier OK" if ok else "check_N5_dixmier FAILED")
    try:
        os.makedirs("logs", exist_ok=True)
        with open("data/n5_dixmier.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N5_dixmier OK" if ok
                       else "check_N5_dixmier FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
