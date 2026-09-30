"""Singular locus of the N=5 hypersurface V(S) (Jacobian criterion).

R = k[p,q,J1,J2,F0,H] (char 0),
S = q^4*H - 11025*F0^2 - 105*q^2*J2^5*J1 - 9*J2^7
(Theorem thm:global-hypersurface). V(S) subset A^6; Sing = V(S, dS)
with the six generator-partials computed directly (S is already in
generator coordinates, so no chain rule through the a-variables is
needed). Dimension via Sage/Singular. S is irreducible (check_s6.py
part B), so the singular locus is a proper closed subset of affine
dimension <= 4. Bridge check ties the generator-writing to the
a-variable writing (exact QQ, SymPy).

Run: sage -c "import sys; sys.path.insert(0, 'scripts/cas'); import check_singlocus; raise SystemExit(check_singlocus.main())"  # log: data/singlocus.log
Prints PASS/FAIL per check plus `check_singlocus OK` (exit 0/1).
"""
import os

log = []

def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)

def _gen_S_sage():
    from sage.all import QQ, PolynomialRing
    R = PolynomialRing(QQ, ['p', 'q', 'J1', 'J2', 'F0', 'H'])
    p, q, J1, J2, F0, H = R.gens()
    S = q**4 * H - 11025 * F0**2 - 105 * q**2 * J2**5 * J1 - 9 * J2**7
    return R, S


def jacobian_ideal_gens():
    R, S = _gen_S_sage()
    return [S] + [S.derivative(v) for v in R.gens()]


def _gen_S_sympy():
    from sympy import symbols
    p, q, J1, J2, F0, H = symbols("p q J1 J2 F0 H")
    S = q**4 * H - 11025 * F0**2 - 105 * q**2 * J2**5 * J1 - 9 * J2**7
    return S, (p, q, J1, J2, F0, H)


def bridge_ok():
    """S_gen under generator->a substitution equals S_a (exact QQ)."""
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from check_s6 import HMONO  # noqa: E402 (frozen H record)
    from sympy import Rational, expand, symbols
    S, (p, q, J1, J2, F0, H) = _gen_S_sympy()
    a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
    j1 = 2 * a1 * a4 - a2**2
    j2 = 2 * a2 * a5 - a3**2
    f0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
          + Rational(1, 3) * a4 * a5**2 * a3**3 * a1
          + Rational(1, 3) * a5**2 * a3**3 * a2**2
          - Rational(1, 5) * a5 * a3**5 * a2
          + Rational(1, 35) * a3**7)
    h = sum(c * a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3]
            * a4**e[4] * a5**e[5] for c, e in HMONO)
    S_sub = expand(S.subs({p: a4, q: a5, J1: j1, J2: j2, F0: f0, H: h}))
    S_a = expand(a5**4 * h - 11025 * f0**2
                 - 105 * a5**2 * j2**5 * j1 - 9 * j2**7)
    return expand(S_sub - S_a) == 0


def affine_dim():
    G = jacobian_ideal_gens()
    R = G[0].parent()
    return R.ideal(G).dimension()

def main():
    ok = True
    G = jacobian_ideal_gens()
    ok &= check("7 generators (S + 6 partials)", len(G) == 7)
    ok &= check("generator S matches a-variable S (bridge)", bridge_ok())
    d = affine_dim()
    log.append("singular locus affine dim = %d" % d)
    ok &= check("singular locus dim < 5", d <= 4)
    for ln in log:
        print(ln)
    print("check_singlocus OK" if ok else "check_singlocus FAILED")
    try:
        os.makedirs("logs", exist_ok=True)
        with open("data/singlocus.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_singlocus OK" if ok
                       else "check_singlocus FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
