"""Check N=6 slice: local slice s with D(s) in K nonzero + localized presentation.

Uses check_A directly (no redefinition)::

    B = k[a_1, ..., a_6],
    D(a_1) = a_2 a_3, D(a_2) = a_3 a_4, D(a_3) = a_4 a_5,
    D(a_4) = a_5 a_6, D(a_5) = D(a_6) = 0,
    G_1 = a_5, G_2 = a_6,
    G_3 = 2a_2a_5 - a_3^2, G_4 = 2a_3a_6 - a_4^2,
    G_5 = 105a_1a_5^2a_6^4 - 105a_2a_3a_4a_5a_6^3 + 35a_2a_4^3a_5a_6^2
         + 35a_3^2a_4^3a_6^2 - 21a_3a_4^5a_6 + 3a_4^7,
    R = k[G_1, ..., G_5] subset K_6 = B^D.

Produces (this task's scope only):
  1. Slice certificate: s = a_4/(a_5a_6) satisfies D(s) = 1, hence D(s)
     is a nonzero element of K_6 (1 lies in every k-subalgebra), while s
     itself is not invariant.
  2. Localized presentation: B_{a_5a_6} = R_{a_5a_6}[s] via explicit
     right-hand sides in R_{a_5a_6}[s] for a_4, a_3, a_2, a_1, with
     denominators verified to be powers of a_5a_6 only.

Out of scope (explicitly NOT asserted here): any global generation claim
B^D = R; global generation stays Conditional on O1 (see paper/10-n6.tex).
This script checks only the slice mechanism over the localization.

SymPy-only (+ stdlib). check_A imported via sys.path-insert of
scripts/cas (apply_D / verify_D).

Run:
    python3 scripts/cas/check_N6_slice.py  # log: data/n6/slice.log
Prints PASS/FAIL per check plus a final `check_slice6 OK` (exit 0/1).
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
    # positions 0..3 are a_1..a_4, 4..5 are a_5,a_6, 6 is s (if present).
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


def _check_slice(a, N):
    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    s = a4 / (a5 * a6)
    Ds = apply_D(s, a, N)
    ok &= _check("D(s)=1 for s=a_4/(a_5a_6)", _is_zero(Ds - 1))
    ok &= _check("D(s) nonzero", not _is_zero(Ds))
    ok &= _check("D(s) in K (verify_D(D(s)))", verify_D(Ds, a, N) is True)
    ok &= _check("1 in R subset K (constants invariant)",
                 verify_D(1, a, N) is True)
    ok &= _check("s itself not invariant", verify_D(s, a, N) is False)
    ok &= _check("denom(s) is an a_5a_6-power",
                 _denom_is_a5a6_power(s, a))
    return ok, s


def _check_localized_presentation(a, N, s):
    from sympy import Symbol, expand

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    s_sym = Symbol("s")
    # Right-hand sides as elements of R_{a_5a_6}[s] (s transcendental here).
    A4s = G1 * G2 * s_sym
    A3s = (G4 + G1**2 * G2**2 * s_sym**2) / (2 * G2)
    A2s = (G3 + A3s**2) / (2 * G1)
    # a_1-free part of G_5, then substituted: N5s must be polynomial.
    N5 = (G5 - 105 * a1 * a5**2 * a6**4)
    N5s = expand(N5).subs({a2: A2s, a3: A3s, a4: A4s})
    A1s = (G5 - N5s) / (105 * G1**2 * G2**4)
    # Denominator structure with s transcendental: powers of a_5a_6 only.
    ok &= _check("denom(A4s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A4s, a, s_sym))
    ok &= _check("denom(A3s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A3s, a, s_sym))
    ok &= _check("denom(A3s) is exactly a_6^1 up to unit",
                 _is_zero(A3s * (2 * G2) - (G4 + G1**2 * G2**2 * s_sym**2)))
    ok &= _check("denom(A2s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A2s, a, s_sym))
    ok &= _check("N5s substituted is a polynomial (constant denominator)",
                 _denom_is_constant(N5s, a, s_sym))
    ok &= _check("denom(A1s) is an a_5a_6-power",
                 _denom_is_a5a6_power(A1s, a, s_sym))
    # Reconstruction: substituting s = a_4/(a_5a_6) recovers each a_i.
    sub = {s_sym: s}
    ok &= _check("a_4=G_1G_2s", _is_zero(A4s.subs(sub) - a4))
    ok &= _check("a_3=(G_4+G_1^2G_2^2s^2)/(2G_2)",
                 _is_zero(A3s.subs(sub) - a3))
    ok &= _check("a_2=(G_3+A3s^2)/(2G_1)", _is_zero(A2s.subs(sub) - a2))
    ok &= _check("a_1=(G_5-N5s)/(105G_1^2G_2^4)",
                 _is_zero(A1s.subs(sub) - a1))
    # Direct rational identities (s as the fraction) for the log record.
    A3 = G4 / (2 * a6) + a5**2 * a6 * s**2 / 2
    A2 = G3 / (2 * a5) + A3**2 / (2 * a5)
    ok &= _check("direct a_3 identity", _is_zero(A3 - a3))
    ok &= _check("direct a_2 identity", _is_zero(A2 - a2))
    return ok


def main():
    ok = True
    N = 6
    a = _vars()
    ok &= _check_table(a, N)
    ok &= _check_kernel_gens(a, N)
    step, s = _check_slice(a, N)
    ok &= step
    ok &= _check_localized_presentation(a, N, s)
    print("check_slice6 OK" if ok else "check_slice6 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
