"""Oracle test for check_N6_weighted_v2 (TDD: written before the module).

The expected values are the exact-QQ SageMath oracle from
data/n6/axis1_sage_probe.log (SageMath 10.9, V_w -> V_w, weights (8,5,3,2,1,1)).

Run:  python3 scripts/cas/test_N6_weighted_v2.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_weighted_v2 import GEN_WTS, dimV, free_count, hyp_count, kerdim


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("generator weights are (1,1,4,6,14)", GEN_WTS == [1, 1, 4, 6, 14])
    ok &= _check("dimV(6)=25", dimV(6) == 25)
    ok &= _check("kerdim(0)=1", kerdim(0) == 1)
    ok &= _check("kerdim(6)=11", kerdim(6) == 11)
    ok &= _check("kerdim(14)=55", kerdim(14) == 55)
    ok &= _check("kerdim(20)=131", kerdim(20) == 131)
    ok &= _check("free_count(14)=55", free_count(GEN_WTS, 14) == 55)
    ok &= _check("free_count(20)=131", free_count(GEN_WTS, 20) == 131)
    ok &= _check("hyp(20)=131 (agrees with free there)", hyp_count(20) == 131)
    ok &= _check("hyp(24)=213 (first excess)", hyp_count(24) == 213)
    ok &= _check("hyp(30)=404", hyp_count(30) == 404)
    print("test_N6_weighted_v2 OK" if ok else "test_N6_weighted_v2 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
