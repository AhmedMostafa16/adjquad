"""Check second exact a0-direction D2 (Phase 7): M = a5^4*a6*G4.

M (total deg 7) admits N (10 terms below, exact-QQ SageMath
inhomogeneous solve, 1656x1287 full rank) with a1a2*M + D6(N) = 0,
i.e. F = a0*M + N is invariant at Fibonacci weight 22.
M is NOT a multiple of the H20-direction a5^4a6^3 (a6-exponents
1,2 < 3): the a0-denominator module has (at least) two generators
already at total degree 7 -- it is NOT principal.

This script (SymPy-only + stdlib) asserts the identity, the uniform
Fibonacci weight 22, and the newness -- all exact over QQ.

Run:
    python3 scripts/cas/check_N6_D2.py  # log: data/n6/D2.log
Prints PASS/FAIL per check plus a final `check_N6_D2 OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402

WT6 = [8, 5, 3, 2, 1, 1]  # a1..a6 (B-level Fibonacci)
WT70 = [13, 8, 5, 3, 2, 1, 1]  # a0..a6

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def _N_terms():
    from sympy import Rational
    return [(Rational(-1, 72), (0, 0, 6, 2, 0, 0)),
            (Rational(5, 756), (0, 0, 7, 0, 0, 1)),
            (Rational(1, 12), (0, 1, 4, 2, 1, 0)),
            (Rational(-1, 54), (0, 1, 5, 0, 1, 1)),
            (Rational(-1, 9), (0, 2, 2, 2, 2, 0)),
            (Rational(-1, 27), (0, 2, 3, 0, 2, 1)),
            (Rational(-1, 9), (1, 0, 2, 3, 2, 0)),
            (Rational(2, 9), (1, 1, 0, 3, 3, 0)),
            (Rational(1, 3), (1, 1, 1, 1, 3, 1)),
            (Rational(-7, 6), (2, 0, 0, 0, 4, 2))]


def _build():
    from sympy import symbols
    a = symbols("a_0:7")
    b = a
    a1, a2, a3, a4, a5, a6 = a[1], a[2], a[3], a[4], a[5], a[6]
    M = a5**4 * a6 * (2 * a3 * a6 - a4**2)
    N = 0
    for co, ex in _N_terms():
        m = co
        for v, p in zip(b[1:], ex):
            m *= v**p
        N += m
    return b, M, N


def D2_invariant():
    from sympy import expand
    b, M, N = _build()
    return expand(b[1] * b[2] * M + apply_D(N, b, 6)) == 0


def D2_Fib_weight():
    from sympy import Poly, symbols
    a = symbols("a_0:7")
    b, M, N = _build()
    F = a[0] * M + N
    wts = set()
    for ex in Poly(F, *a).as_dict():
        wts.add(sum(e * w for e, w in zip(ex, WT70)))
    return wts.pop() if len(wts) == 1 else -1


def D2_M_is_new():
    """M = a5^4*a6*G4 not divisible by a5^4*a6^3 (a6-exps 1,2 < 3)."""
    from sympy import Poly, symbols
    b, M, _ = _build()
    return min(e[6] for e in Poly(M, *b).as_dict()) < 3


def main():
    from sympy import Poly, symbols
    ok = True
    b, M, N = _build()
    ok &= check("a1a2*M + D6(N) = 0", D2_invariant() is True)
    ok &= check("D6(N) = -a1a2*M (direct)",
                __import__("sympy").expand(
                    apply_D(N, b, 6) + b[1] * b[2] * M) == 0)
    ok &= check("Fibonacci weight 22", D2_Fib_weight() == 22)
    ok &= check("10-term N", len(Poly(N, *b).as_dict()) == 10)
    ok &= check("M not multiple of a5^4a6^3", D2_M_is_new() is True)
    for ln in log:
        print(ln)
    print("check_N6_D2 OK" if ok else "check_N6_D2 FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/D2.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N6_D2 OK" if ok
                       else "check_N6_D2 FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
