"""Oracle test for check_N7_Bweighted (TDD: written before the module).

Structural facts only (recon hunt): kerdim(0) = 1, kerdim(1) = 2
(sinks a6, a7). B7 = k[a1..a7], weights (13,8,5,3,2,1,1).

Run:  python3 scripts/cas/test_N7_Bweighted.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N7_Bweighted import GEN_WTS_GUESS, free_count, kerdim


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("kerdim(0)=1", kerdim(0) == 1)
    ok &= _check("kerdim(1)=2", kerdim(1) == 2)
    ok &= _check("free_count sanity", free_count([1, 1], 2) == 3)
    ok &= _check("guess weights recorded", len(GEN_WTS_GUESS) >= 2)
    print("test_N7_Bweighted OK" if ok else "test_N6_Bweighted FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
