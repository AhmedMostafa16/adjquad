"""Oracle test for check_N6_F0 (TDD: written before the module).

Oracle: the exact-QQ SageMath restricted solve (/tmp/opencode/f0_6_restricted.py):
F0_6 = c6^2*a0 + G' with 12-term G', D6(F0_6) = 0, a0-coefficient c6^2,
uniform Fibonacci weight 25 (wt(a0) = 13).

Run:  python3 scripts/cas/test_N6_F0.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_F0 import F0_6_a0coeff_is_c6sq, F0_6_invariant, F0_6_weight


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("D6(F0_6) = 0", F0_6_invariant() is True)
    ok &= _check("a0-coefficient is c6^2", F0_6_a0coeff_is_c6sq() is True)
    ok &= _check("uniform weight 25", F0_6_weight() == 25)
    print("test_N6_F0 OK" if ok else "test_N6_F0 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
