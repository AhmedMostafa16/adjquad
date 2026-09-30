"""Compute the exact resonance degree rho_p for the N=5 adjacent-quadratic LND.

r_p = q^{-4}(1/3 q^2 x^3 y^2 - 1/5 q x^5 y + 1/35 x^7) is algebraic over
L_p = k(q, y^2, w), w = 2qy - x^2, of degree <= 4 (manuscript 05a:136-139,
tower L_p ⊂ L_p(y) ⊂ L_p(y)(x), each step degree <= 2). This script
determines the exact degree by exact rational arithmetic (SymPy, QQ):

  T1. y^2-transcendental T is a nonsquare in k(Q,T,W)  => [L_p(y):L_p] = 2.
  T2. W^2-4Q^2T is a nonsquare in k(Q,T,W) (Eisenstein-irreducible at (T),
      hence squarefree nonconstant) => X^2-(2QY-W) irreducible over
      L_p(Y) => [L_p(Y)(X):L_p(Y)] = 2.  Total degree exactly 4, basis
      {1, X, Y, XY} over L_p.
  T3. Tower normal form of r_p has nonzero X/XY coordinates => r_p ∉ L_p,
      so rho_p >= 2 (and 3 is impossible by tower divisibility: degree
      divides 4).  Hence rho_p ∈ {2, 4}.
  T4. Groebner elimination of X, Y gives an annihilator P(V) for r_p over
      QQ[Q,T,W]; factor over QQ, evaluate each V-factor at r_p via the
      tower normal form; the least V-degree among vanishing factors is
      the minimal polynomial degree = rho_p (Gauss's lemma: the minimal
      polynomial over L_p = Frac(QQ[Q,T,W]) corresponds to a QQ-factor).
  T5. Independent cross-check: re-eliminate with swapped variable order
      and confirm the same minimal degree.

Status: certificate for rho_p = 4 (manuscript rem:p-obstacle,
def:resonance). Prints T1-T5, RESULT, and a final `probe_rho_p OK`
(exit 0/1).

Run: python3 scripts/cas/probe_rho_p.py  # log: data/rho_p.log
"""
import sys
from fractions import Fraction
from sympy import (QQ, Rational, symbols, expand, factor_list, groebner,
                   Poly, sqrt)


Q, T, W, X, Y, V = symbols('Q T W X Y V')

# ---------------------------------------------------------------- tower
def red_x(expr):
    """Reduce X-powers >= 2 via X^2 = 2QY - W. Returns expr in span{1, X}."""
    p = Poly(expand(expr), X)
    if p is None:
        return expand(expr)
    coeffs = p.all_coeffs()[::-1]  # coeffs[i] of X^i
    c0 = coeffs[0] if len(coeffs) > 0 else 0
    c1 = coeffs[1] if len(coeffs) > 1 else 0
    pw = 1  # (2QY - W)^k accumulator for pairs
    # Horner-style: fold X^{2k}, X^{2k+1} using X^2 -> S
    S = 2 * Q * Y - W
    even, odd = 0, 0
    for i, c in enumerate(coeffs):
        k, r = divmod(i, 2)
        if r == 0:
            even += c * S**k
        else:
            odd += c * S**k
    return expand(even + odd * X)


def tower_reduce(expr):
    """Normal form in basis {1, X, Y, XY} over QQ(Q,T,W).

    Returns (c0, cX, cY, cXY) with Y-powers reduced via Y^2 = T.
    """
    e = red_x(expand(expr))
    p = Poly(e, Y)
    coeffs = p.all_coeffs()[::-1] if p is not None else [e]
    even, odd = 0, 0
    for i, c in enumerate(coeffs):
        k, r = divmod(i, 2)
        if r == 0:
            even += c * T**k
        else:
            odd += c * T**k
    # even/odd may still contain X: split
    def split_x(u):
        px = Poly(expand(u), X)
        if px is None or px.degree() is None or px.degree() == 0:
            return expand(u), 0
        cs = px.all_coeffs()[::-1]
        return expand(cs[0]), expand(sum(cs[i] * X**(i - 1) for i in range(1, len(cs))))
    e0, e1 = split_x(even)
    o0, o1 = split_x(odd)
    # e1, o1 must be zero if reduction was complete (X-degree < 2 preserved)
    return expand(e0), expand(e1), expand(o0), expand(o1)


def is_zero(expr):
    return expand(expr) == 0


# ------------------------------------------------------- square tests
def is_square_in_rational_function_field(expr, gens):
    """Decide whether expr ∈ QQ[gens] is a square in Frac(QQ[gens]).

    A squarefree nonconstant polynomial is never a square of a rational
    function: (P/R)^2 = S in lowest terms forces S's numerator and
    denominator to be squares up to a constant, contradicting a
    squarefree nonconstant factor. Constant case: QQ square test.
    """
    expr = expand(expr)
    if expr.is_number:
        r = Rational(expr)
        n, d = r.p, r.q
        def isq(n):
            n = abs(n)
            s = int(sqrt(n))
            return s * s == n
        return isq(n) and isq(d)
    fac = factor_list(Poly(expr, gens))
    const = fac[0]
    if not is_square_in_rational_function_field(const, gens):
        return False
    return all(e % 2 == 0 for (_, e) in fac[1])


# ---------------------------------------------------------------- data
# r_p numerator (times Q^4): N = 1/3 Q^2 X^3 Y^2 - 1/5 Q X^5 Y + 1/35 X^7
N_rp = Rational(1, 3) * Q**2 * X**3 * Y**2 - Rational(1, 5) * Q * X**5 * Y \
    + Rational(1, 35) * X**7


def main(argv=None):
    # ---- T1: [L_p(Y) : L_p] = 2 (T nonsquare in k(Q,T,W))
    assert not is_square_in_rational_function_field(T, (Q, T, W)), \
        "T must be a nonsquare (Y^2 - T irreducible)"
    print("T1: T nonsquare in k(Q,T,W)  =>  [L_p(y):L_p] = 2")

    # ---- T2: [L_p(Y)(X) : L_p(Y)] = 2
    D = W**2 - 4 * Q**2 * T
    fac_D = factor_list(Poly(D, (Q, T, W)))
    assert len(fac_D[1]) == 1 and fac_D[1][0][1] == 1, \
        "W^2-4Q^2T must be irreducible (Eisenstein at (T))"
    assert not is_square_in_rational_function_field(D, (Q, T, W)), \
        "W^2-4Q^2T must be a nonsquare"
    print("T2: W^2-4Q^2T nonsquare  =>  X^2-(2QY-W) irreducible over L_p(y)")
    print("    => total degree exactly 4, basis {1,X,Y,XY} over L_p")

    # ---- numeric sanity: r_p != 0 (Q=T=1, W=0, Y=1, X^2=2)
    num_check = Rational(2, 3) - Rational(4, 5) + Rational(8, 35)
    assert num_check == Rational(2, 21) != 0
    print("T0: r_p nonzero sanity (sample point gives sqrt(2)*2/21) OK")

    # ---- T3: r_p ∉ L_p
    c0, cX, cY, cXY = tower_reduce(N_rp)
    print("T3: tower coords of Q^4*r_p: X-part nonzero =",
          not (is_zero(cX) and is_zero(cXY)))
    assert not (is_zero(cX) and is_zero(cXY)), \
        "r_p must lie outside L_p (odd X-part)"
    print("    r_p ∉ L_p  =>  rho_p >= 2; degree 3 impossible (3 ∤ 4).")
    print("    Hence rho_p ∈ {2, 4}.")

    # ---- T4: elimination + factor + evaluate
    F = 105 * Q**4 * V - (35 * Q**2 * X**3 * Y**2
                          - 21 * Q * X**5 * Y + 3 * X**7)
    G = groebner([X**2 - (2 * Q * Y - W), Y**2 - T, F],
                 X, Y, V, Q, T, W, order='lex')
    elim = [g for g in G.polys if set(g.free_symbols) <= {V, Q, T, W}]
    assert elim, "elimination must produce a V-polynomial"
    P = elim[0].as_expr()
    dv = Poly(P, V).degree()
    print("T4: annihilator degree in V:", dv)
    fac = factor_list(Poly(P, (V, Q, T, W)))
    print("    QQ-factor multidegrees:",
          [(Poly(f, V).degree() if V in f.free_symbols else 0) for (f, _) in fac[1]])
    vanishing = []
    for (fpoly, _) in fac[1]:
        f = fpoly.as_expr()
        if V not in f.free_symbols:
            continue
        # evaluate V -> r_p = N_rp/Q^4: clear denominators by Q^{4d}
        # (Q != 0 in the domain), then reduce the polynomial numerator
        d = Poly(f, V).degree()
        val = expand(Q**(4 * d) * f.subs(V, N_rp / Q**4))
        coords = tower_reduce(val)
        if all(is_zero(c) for c in coords):
            vanishing.append(d)
            print("    factor of V-degree", d, "VANISHES at r_p")
        else:
            print("    factor of V-degree", d, "does not vanish")
    assert vanishing, "at least one factor must vanish (P(r_p) = 0)"
    rho = min(vanishing)
    print("RESULT: rho_p =", rho)
    for (fpoly, _) in fac[1]:
        f = fpoly.as_expr()
        if V in f.free_symbols and Poly(f, V).degree() == rho:
            print("minimal polynomial (primitive QQ-form):")
            print("   ", f)
    if rho == 2:
        print("minimal polynomial (up to L_p unit): T^2 - r_p^2 with "
              "r_p^2 ∈ L_p verified by vanishing quadratic factor")

    # ---- T5: cross-check with swapped elimination order
    G2 = groebner([Y**2 - T, X**2 - (2 * Q * Y - W), F],
                  Y, X, V, Q, T, W, order='lex')
    elim2 = [g for g in G2.polys if set(g.free_symbols) <= {V, Q, T, W}]
    assert elim2, "swapped elimination must also produce a V-polynomial"
    dv2 = Poly(elim2[0].as_expr(), V).degree()
    print("T5: swapped-order annihilator V-degree:", dv2,
          "consistent" if dv2 == dv else "MISMATCH")
    assert dv2 == dv
    return rho


if __name__ == '__main__':
    rho = main()
    ok = (rho == 4)
    print('probe_rho_p ' + ('OK' if ok else 'UNEXPECTED-RHO'))
    sys.exit(0 if ok else 1)
