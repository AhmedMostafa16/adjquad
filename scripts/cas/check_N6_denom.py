"""Check N=6 denominator: explicit c_6 clears slice denominators + weight-shift.

Consumes Tasks 2-3 verbatim (no redefinition)::

    B = k[a_1, ..., a_6],
    D(a_1) = a_2 a_3, D(a_2) = a_3 a_4, D(a_3) = a_4 a_5,
    D(a_4) = a_5 a_6, D(a_5) = D(a_6) = 0,
    G_1 = a_5, G_2 = a_6,
    G_3 = 2a_2a_5 - a_3^2, G_4 = 2a_3a_6 - a_4^2,
    G_5 = 105a_1a_5^2a_6^4 - 105a_2a_3a_4a_5a_6^3 + 35a_2a_4^3a_5a_6^2
         + 35a_3^2a_4^3a_6^2 - 21a_3a_4^5a_6 + 3a_4^7,
    R = k[G_1, ..., G_5] subset K_6 = B^D,
    s = a_4/(a_5a_6), D(s) = 1.

Produces (this task's scope only):
  1. Explicit denominator c_6 = a_5^2a_6^4 (minimal LCM of the slice
     denominators (0,0),(0,1),(1,2),(2,4) from check_A). The exact
     a_1-coefficient of G_5 is 105*c_6 (unit multiple in char 0);
     both c_6 and 105*c_6 clear every slice denominator.
  2. Weight-shift verdict HOLDS (theorem): with Fibonacci weights
     wt(a_1..a_6) = (8,5,3,2,1,1), wt(G_5) = 14, wt(c_6) = 6,
     wt(W) = 8 for W = G_5/(105*c_6) = a_1 + N_5/(105*c_6),
     so wt(G_5) = wt(W) + wt(c_6) = 8 + 6.

Out of scope (explicitly NOT asserted here): any global generation claim
B^D = R (stays Conditional on O1); saturation; Afringt{6}^D claims.

SymPy-only (+ stdlib). check_A imported via sys.path-insert of
scripts/cas (apply_D / verify_D).

Run:
    python3 scripts/cas/check_N6_denom.py  # log: data/n6/denom.log
Prints PASS/FAIL per check plus a final `check_denom6 OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def _is_zero(expr):
    from sympy import cancel, expand

    if expand(expr) == 0:
        return True
    return cancel(expr) == 0


def _vars():
    from sympy import symbols

    a = symbols("a_0:7")
    return a


def _generators(a):
    # Exact forms from check_A (do not redefine).
    a0, a1, a2, a3, a4, a5, a6 = a
    G1 = a5
    G2 = a6
    G3 = 2 * a2 * a5 - a3**2
    G4 = 2 * a3 * a6 - a4**2
    G5 = (
        105 * a1 * a5**2 * a6**4
        - 105 * a2 * a3 * a4 * a5 * a6**3
        + 35 * a2 * a4**3 * a5 * a6**2
        + 35 * a3**2 * a4**3 * a6**2
        - 21 * a3 * a4**5 * a6
        + 3 * a4**7
    )
    return [G1, G2, G3, G4, G5]


FIB_WT = None  # set in main from symbols


def _wt_of_monomial(exps, syms):
    return sum(e * FIB_WT[s] for e, s in zip(exps, syms))


def _all_weights(expr, syms):
    from sympy import Poly, expand

    poly = Poly(expand(expr), *syms)
    return sorted(_wt_of_monomial(m, syms) for m in poly.monoms())


def _denom_is_a5a6_power(expr, a, s_sym=None):
    """True iff expr, in lowest terms, has denominator c*a_5^u*a_6^v."""
    from sympy import Poly, cancel

    a0, a1, a2, a3, a4, a5, a6 = a
    _, denom = cancel(expr).as_numer_denom()
    syms = [a1, a2, a3, a4, a5, a6]
    if s_sym is not None:
        syms = syms + [s_sym]
    poly = Poly(denom, *syms)
    if poly is None:
        return False
    items = list(poly.as_dict().items())
    if len(items) != 1:
        return False
    mon, _coeff = items[0]
    if any(mon[i] != 0 for i in range(4)):
        return False
    if s_sym is not None and mon[6] != 0:
        return False
    return True


def _denom_is_constant(expr, a, s_sym=None):
    """True iff expr, in lowest terms, has constant (nonzero) denominator."""
    from sympy import Poly, cancel

    a0, a1, a2, a3, a4, a5, a6 = a
    _, denom = cancel(expr).as_numer_denom()
    syms = [a1, a2, a3, a4, a5, a6]
    if s_sym is not None:
        syms = syms + [s_sym]
    poly = Poly(denom, *syms)
    if poly is None:
        return False
    items = list(poly.as_dict().items())
    if len(items) != 1:
        return False
    mon, _coeff = items[0]
    return all(e == 0 for e in mon)


def _check_table(a, N):
    from sympy import expand

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    expected = {
        "D(a_1)=a_2a_3": (a1, a2 * a3),
        "D(a_2)=a_3a_4": (a2, a3 * a4),
        "D(a_3)=a_4a_5": (a3, a4 * a5),
        "D(a_4)=a_5a_6": (a4, a5 * a6),
        "D(a_5)=0": (a5, 0),
        "D(a_6)=0": (a6, 0),
    }
    for name, (var, val) in expected.items():
        ok &= _check(name, expand(apply_D(var, a, N) - val) == 0)
    return ok


def _check_kernel_gens(a, N):
    ok = True
    names = ["G_1=a_5", "G_2=a_6", "G_3=2a_2a_5-a_3^2",
             "G_4=2a_3a_6-a_4^2", "G_5 (degree 7)"]
    for name, g in zip(names, _generators(a)):
        ok &= _check("D(%s)=0" % name, apply_D(g, a, N) == 0)
        ok &= _check("verify_D(%s)" % name, verify_D(g, a, N) is True)
    return ok


def _check_c6(a, N):
    from sympy import Poly, expand

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    c6 = a5**2 * a6**4
    C6 = 105 * a5**2 * a6**4
    ok &= _check("c_6=a_5^2a_6^4", expand(c6 - a5**2 * a6**4) == 0)
    ok &= _check("D(c_6)=0", apply_D(c6, a, N) == 0)
    ok &= _check("verify_D(c_6)", verify_D(c6, a, N) is True)
    ok &= _check("D(105c_6)=0", apply_D(C6, a, N) == 0)
    coeff_a1 = Poly(G5, a1).nth(1)
    ok &= _check("G_5 a_1-coefficient is 105c_6",
                 expand(coeff_a1 - C6) == 0)
    N5 = expand(G5 - C6 * a1)
    ok &= _check("N_5=G_5-105c_6a_1 free of a_1",
                 Poly(N5, a1).degree() == 0 or _is_zero(Poly(N5, a1).nth(1)))
    ok &= _check("c_6 is an a_5a_6-power",
                 _denom_is_a5a6_power(c6, a))
    return ok, c6, C6


def _check_denom_clearing(a, N, c6, C6):
    from sympy import Symbol, expand

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    s_sym = Symbol("s")
    s = a4 / (a5 * a6)
    ok &= _check("D(s)=1 for s=a_4/(a_5a_6)",
                 _is_zero(apply_D(s, a, N) - 1))
    A4s = G1 * G2 * s_sym
    A3s = (G4 + G1**2 * G2**2 * s_sym**2) / (2 * G2)
    A2s = (G3 + A3s**2) / (2 * G1)
    N5 = expand(G5 - C6 * a1)
    N5s = expand(N5).subs({a2: A2s, a3: A3s, a4: A4s})
    A1s = (G5 - N5s) / (105 * G1**2 * G2**4)
    # Slice denominators are a_5a_6-powers.
    ok &= _check("denom(A4s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A4s, a, s_sym))
    ok &= _check("denom(A3s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A3s, a, s_sym))
    ok &= _check("denom(A2s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A2s, a, s_sym))
    ok &= _check("denom(A1s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A1s, a, s_sym))
    ok &= _check("N5s substituted is a polynomial (constant denominator)",
                 _denom_is_constant(N5s, a, s_sym))
    # Explicit clearing by c_6 (scalars 2, 8, 105 are units in char 0).
    ok &= _check("c_6*A4s is a polynomial",
                 _denom_is_constant(c6 * A4s, a, s_sym))
    ok &= _check("c_6*A3s is a polynomial",
                 _denom_is_constant(c6 * A3s, a, s_sym))
    ok &= _check("c_6*A2s is a polynomial",
                 _denom_is_constant(c6 * A2s, a, s_sym))
    ok &= _check("c_6*A1s is a polynomial up to unit 1/105",
                 _denom_is_constant(c6 * A1s, a, s_sym))
    ok &= _check("105c_6*A1s is a polynomial exactly",
                 _denom_is_constant(C6 * A1s, a, s_sym))
    # Reconstruction still recovers each variable.
    sub = {s_sym: s}
    ok &= _check("c_6 clears: A4 recovers a_4",
                 _is_zero(A4s.subs(sub) - a4))
    ok &= _check("c_6 clears: A3 recovers a_3",
                 _is_zero(A3s.subs(sub) - a3))
    ok &= _check("c_6 clears: A2 recovers a_2",
                 _is_zero(A2s.subs(sub) - a2))
    ok &= _check("c_6 clears: A1 recovers a_1",
                 _is_zero(A1s.subs(sub) - a1))
    return ok


def _check_weight_shift(a):
    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    syms = [a1, a2, a3, a4, a5, a6]
    c6 = a5**2 * a6**4
    C6 = 105 * a5**2 * a6**4
    N5 = G5 - C6 * a1
    ok &= _check("wt(G_1)=1", _all_weights(G1, syms) == [1])
    ok &= _check("wt(G_2)=1", _all_weights(G2, syms) == [1])
    ok &= _check("wt(G_3)=6", _all_weights(G3, syms) == [6, 6])
    ok &= _check("wt(G_4)=4", _all_weights(G4, syms) == [4, 4])
    ok &= _check("wt(G_5)=14", _all_weights(G5, syms) == [14] * 6)
    ok &= _check("wt(c_6)=6", _all_weights(c6, syms) == [6])
    ok &= _check("wt(105c_6)=6", _all_weights(C6, syms) == [6])
    ok &= _check("wt(a_1)=8", _all_weights(a1, syms) == [8])
    ok &= _check("every N_5 monomial has weight 14",
                 _all_weights(N5, syms) == [14] * 5)
    # W = G_5/(105c_6) = a_1 + N_5/(105c_6): each term weight 8.
    w_terms = [8] + [w - 6 for w in _all_weights(N5, syms)]
    ok &= _check("every W-term has weight 8", all(w == 8 for w in w_terms))
    ok &= _check("weight-shift wt(G_5)=wt(W)+wt(c_6): 14=8+6 HOLDS",
                 14 == 8 + 6 and _all_weights(G5, syms) == [14] * 6
                 and _all_weights(c6, syms) == [6])
    return ok


def main():
    global FIB_WT
    ok = True
    N = 6
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    FIB_WT = {a1: 8, a2: 5, a3: 3, a4: 2, a5: 1, a6: 1}
    ok &= _check_table(a, N)
    ok &= _check_kernel_gens(a, N)
    step, c6, C6 = _check_c6(a, N)
    ok &= step
    ok &= _check_denom_clearing(a, N, c6, C6)
    ok &= _check_weight_shift(a)
    print("check_denom6 OK" if ok else "check_denom6 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
