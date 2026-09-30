"""Oracle test for check_N6_multfloor (TDD: written before the module).

Oracle: on the a6-side, r_6 = a4^7/(35a5^2) = alpha*sbar with
alpha = -z4^3/(35z1), sbar = a4/a5, sbar^2 = -z4/z1^2 in L_6.
Hence m(T) = T^2 + alpha^2*z4/z1^2 has m(r_6) = 0 (simple root:
m'(r_6) = 2r_6 != 0), i.e. minpoly degree exactly 2.

Run:  python3 scripts/cas/test_N6_multfloor.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_multfloor import minpoly_eval_zero, minpoly_simple


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("m(r_6) = 0", minpoly_eval_zero() is True)
    ok &= _check("m'(r_6) != 0 (simple root)", minpoly_simple() is True)
    print("test_N6_multfloor OK" if ok else "test_N6_multfloor FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
