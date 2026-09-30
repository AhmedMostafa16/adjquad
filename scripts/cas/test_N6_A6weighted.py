"""Oracle test for check_N6_A6weighted (TDD: written before the module).

Structural facts only (the probe is a hunt; its table IS the unknown):
kerdim(0) = 1, kerdim(1) = 2 (a5, a6), free-count sanity on
(1,1,4,6,14,25).

Run:  python3 scripts/cas/test_N6_A6weighted.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_A6weighted import GEN_WTS, free_count, kerdim


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("generator weights (1,1,4,6,14,25)",
                 GEN_WTS == [1, 1, 4, 6, 14, 25])
    ok &= _check("kerdim(0)=1", kerdim(0) == 1)
    ok &= _check("kerdim(1)=2", kerdim(1) == 2)
    ok &= _check("free_count(0)=1", free_count(GEN_WTS, 0) == 1)
    print("test_N6_A6weighted OK" if ok else "test_N6_A6weighted FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
