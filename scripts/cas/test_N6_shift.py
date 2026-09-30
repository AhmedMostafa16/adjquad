"""Oracle test for check_N6_shift (TDD: written before the module).

Oracle: the graded shift isomorphism phi : (A5,D5) -> (B,D6|_B),
a_i |-> a_{i+1}, intertwines (all six generators) and transports the
N=5 hypersurface verdict: H_B (wt 24, a1-degree 2, D6 = 0) refutes
B-level five-generation; S_B = 0 is the transported relation.

Run:  python3 scripts/cas/test_N6_shift.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_shift import (HB_a1deg_two, HB_invariant, R24_a1deg_le_one,
                            SB_zero, intertwines)


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("shift intertwines on all generators", intertwines() is True)
    ok &= _check("D6(H_B) = 0", HB_invariant() is True)
    ok &= _check("H_B has a1-degree 2", HB_a1deg_two() is True)
    ok &= _check("R_24 has a1-degree <= 1", R24_a1deg_le_one() is True)
    ok &= _check("S_B = 0", SB_zero() is True)
    print("test_N6_shift OK" if ok else "test_N6_shift FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
