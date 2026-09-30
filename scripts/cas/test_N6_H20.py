"""Oracle test for check_N6_H20 (TDD: written before the module).

Oracle: exact-QQ SageMath null-vector (support stable across 3 primes,
D6 = 0 verified exactly): H20 of weight 20, a0-degree 1 with a0-part
a0*a5^4*a6^3, outside k[G1..G5,F0_6] (free span at wt 20 is a0-free).

Run:  python3 scripts/cas/test_N6_H20.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_H20 import (H20_a0coeff, H20_invariant, H20_outside_free,
                          H20_weight, F0_6_in_H20_plus_K6)


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("D6(H20) = 0", H20_invariant() is True)
    ok &= _check("a0-coefficient is a5^4*a6^3", H20_a0coeff() is True)
    ok &= _check("uniform weight 20", H20_weight() == 20)
    ok &= _check("H20 outside k[G,F0_6]", H20_outside_free() is True)
    ok &= _check("F0_6 in a6^5*H20 + K6", F0_6_in_H20_plus_K6() is True)
    print("test_N6_H20 OK" if ok else "test_N6_H20 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
