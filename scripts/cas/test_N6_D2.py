"""Oracle test for check_N6_D2 (TDD: written before the module).

Oracle: exact-QQ SageMath inhomogeneous solve (1656x1287, full rank):
M = a5^4*a6*G4 (total deg 7) admits N (10 terms) with
a1a2*M + D6(N) = 0, i.e. a0*M + N is invariant at Fibonacci weight 22.
Second exact a0-direction after H20.

Run:  python3 scripts/cas/test_N6_D2.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_D2 import D2_Fib_weight, D2_invariant, D2_M_is_new


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("a1a2*M + D6(N) = 0 exactly", D2_invariant() is True)
    ok &= _check("Fibonacci weight 22", D2_Fib_weight() == 22)
    ok &= _check("M not a multiple of a5^4a6^3", D2_M_is_new() is True)
    print("test_N6_D2 OK" if ok else "test_N6_D2 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
