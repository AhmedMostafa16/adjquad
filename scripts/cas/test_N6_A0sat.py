"""Oracle test for check_N6_A0sat (TDD: written before the module).

Oracle: the two exact master identities (consequences of the
Established invariances D6(F0_6) = 0 and D6(H20) = 0):
  D6(G') = -c6^2*a1a2  (G' = F0_6 - c6^2*a0),
  D6(f0) = -a1a2*a5^4*a6^3  (f0 = H20 - a0*a5^4*a6^3),
plus projection facts: the a5^4a6^3-direction is present at m = 7,
nothing below it (m = 6 gives goods 0).

Run:  python3 scripts/cas/test_N6_A0sat.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_A0sat import (c6sq_witness, goods_dim, h20dir_witness,
                            no_direction_below)


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("c6^2 master identity", c6sq_witness() is True)
    ok &= _check("a5^4a6^3 master identity", h20dir_witness() is True)
    ok &= _check("no direction at m=6", no_direction_below() is True)
    ok &= _check("a5^4a6^3-direction present at m=7", goods_dim(7) >= 1)
    print("test_N6_A0sat OK" if ok else "test_N6_A0sat FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
