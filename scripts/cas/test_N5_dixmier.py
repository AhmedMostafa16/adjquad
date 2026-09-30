"""Oracle test for check_N5_dixmier (TDD: written before the module).

Oracle: the x-basis ledger of T = sum e_k s^{k+1}/(k+1) over
Frac(k[a1,a2,a4,a5])[x] (exploration /tmp/opencode/denom_ledger.py):
  x^7: -1/(p^2 q^4), x^5: a2/(p^2 q^3),
  x^3: -(a1a4^2a5^2+a2^2a4a5^2)/(p^3 q^4), x^1: a1a2/(pq),
and no other x-powers.

Run:  python3 scripts/cas/test_N5_dixmier.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N5_dixmier import x_coeffs


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    d = x_coeffs()
    ok &= _check("x-support is {1,3,5,7}", sorted(d) == [1, 3, 5, 7])
    ok &= _check("top denom is p^2q^4", d[7][1] == (2, 4))
    ok &= _check("x^5 denom is p^2q^3", d[5][1] == (2, 3))
    ok &= _check("x^3 denom is p^3q^4", d[3][1] == (3, 4))
    ok &= _check("x^1 denom is pq", d[1][1] == (1, 1))
    print("test_N5_dixmier OK" if ok else "test_N5_dixmier FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
