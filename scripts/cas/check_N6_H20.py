"""Check N=6 A6 hidden generator H20 (Phase 6): A6^D strictly exceeds k[G,F0_6].

H20 (weight 20, a0-degree 1, 12 terms) satisfies D6(H20) = 0 with
a0-coefficient a5^4*a6^3. At weight 20 the free span of k[G1..G5,F0_6]
is a0-free (F0_6 weighs 25 > 20; G1..G5 are a0-free), while H20 has
nonzero a0-part -- hence H20 not in k[G1..G5,F0_6] UNCONDITIONALLY
(no B-generation needed), and A6^D6 strictly contains k[G,F0_6].
First excess is exactly at weight 20 (exact-QQ A6 probe through 20).

This script (SymPy-only + stdlib) asserts D6(H20) = 0, the a0-form,
uniform weight 20, and the outside-free-span certificate -- all exact
over QQ. The full A6 ring (relations, series) stays Open.

Run:
    python3 scripts/cas/check_N6_H20.py  # log: data/n6/H20.log
Prints PASS/FAIL per check plus a final `check_N6_H20 OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402

WT = [13, 8, 5, 3, 2, 1, 1]  # a0..a6

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def _H20_terms():
    from sympy import Rational
    return [(Rational(-19, 480), [0, 0, 0, 4, 4, 0, 0]),
            (Rational(293, 1800), [0, 0, 0, 5, 2, 0, 1]),
            (Rational(-49, 450), [0, 0, 0, 6, 0, 0, 2]),
            (Rational(19, 120), [0, 0, 1, 2, 4, 1, 0]),
            (Rational(-59, 90), [0, 0, 1, 3, 2, 1, 1]),
            (Rational(59, 180), [0, 0, 1, 4, 0, 1, 2]),
            (Rational(-1, 8), [0, 0, 2, 0, 4, 2, 0]),
            (Rational(1, 2), [0, 0, 2, 1, 2, 2, 1]),
            (Rational(-1, 15), [0, 1, 0, 0, 5, 2, 0]),
            (Rational(1, 3), [0, 1, 0, 1, 3, 2, 1]),
            (Rational(-1, 1), [0, 1, 1, 0, 1, 3, 2]),
            (Rational(1, 1), [1, 0, 0, 0, 0, 4, 3])]


def _H20(a):
    H = 0
    for co, ex in _H20_terms():
        m = co
        for v, p in zip(a, ex):
            m *= v**p
        H += m
    return H


def H20_invariant():
    from sympy import symbols, expand
    a = symbols("a_0:7")
    return expand(apply_D(_H20(a), a, 6)) == 0


def H20_a0coeff():
    from sympy import Poly, expand, symbols
    a = symbols("a_0:7")
    H = _H20(a)
    return (Poly(H, a[0]).degree() == 1
            and expand(Poly(H, a[0]).nth(1) - a[5]**4 * a[6]**3) == 0)


def H20_weight():
    from sympy import Poly, symbols
    a = symbols("a_0:7")
    wts = set()
    for ex in Poly(_H20(a), *a).as_dict():
        wts.add(sum(e * w for e, w in zip(ex, WT)))
    return wts.pop() if len(wts) == 1 else -1


def F0_6_in_H20_plus_K6():
    """F0_6 - a6^5*H20 is a0-free and D6-invariant (hence in K6):
    F0_6 adds no new a0-direction beyond H20."""
    from sympy import expand, symbols
    from check_N6_F0 import _F0_6
    a = symbols("a_0:7")
    F, _, _ = _F0_6(a)
    K0 = expand(F - a[6]**5 * _H20(a))
    return (a[0] not in K0.free_symbols
            and expand(apply_D(K0, a, 6)) == 0)


def H20_outside_free():
    """Free span of k[G,F0_6] at wt 20 is a0-free; H20 is not."""
    from sympy import Poly, symbols
    a = symbols("a_0:7")
    H = _H20(a)
    if Poly(H, a[0]).degree() != 1:
        return False
    # F0_6 weighs 25 > 20: only G-monomials (a0-free by construction).
    # G1..G5 involve a1..a6 only (check_N6_kernel.py), so every wt-20
    # free monomial is a0-free, while H20 has a0-degree 1.
    gens_involve_a0 = any(
        a[0] in g.free_symbols
        for g in _G_gens(a))
    return not gens_involve_a0


def _G_gens(a):
    a1, a2, a3, a4, a5, a6 = a[1], a[2], a[3], a[4], a[5], a[6]
    return [a5, a6, 2 * a2 * a5 - a3**2, 2 * a3 * a6 - a4**2,
            105 * a1 * a5**2 * a6**4
            - 105 * a2 * a3 * a4 * a5 * a6**3
            + 35 * a2 * a4**3 * a5 * a6**2
            + 35 * a3**2 * a4**3 * a6**2
            - 21 * a3 * a4**5 * a6 + 3 * a4**7]


def main():
    from sympy import Poly, symbols
    ok = True
    N = 6
    a = symbols("a_0:7")
    H = _H20(a)
    ok &= check("D6(H20)=0", verify_D(H, a, N) is True)
    ok &= check("D6(H20)=0 (direct)", H20_invariant() is True)
    ok &= check("a0-degree 1, a0-coeff a5^4*a6^3", H20_a0coeff() is True)
    ok &= check("uniform Fibonacci weight 20", H20_weight() == 20)
    ok &= check("12 terms", len(Poly(H, *a).as_dict()) == 12)
    ok &= check("H20 outside k[G,F0_6] (a0-part vs a0-free span)",
                H20_outside_free() is True)
    ok &= check("F0_6 in a6^5*H20 + K6 (no new direction)",
                F0_6_in_H20_plus_K6() is True)
    for ln in log:
        print(ln)
    print("check_N6_H20 OK" if ok else "check_N6_H20 FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/H20.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N6_H20 OK" if ok
                       else "check_N6_H20 FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
