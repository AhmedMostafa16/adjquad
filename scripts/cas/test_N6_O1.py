"""Oracle test for check_N6_O1 (TDD: written before the module).

Oracle: the exact-SymPy `t1` stats of scripts/cas/check_N6_kernel.py
(nulldim, goods) = (5,0),(8,0),(14,0),(20,0),(30,0) for m = 1..5 and
(41,1) for m = 6, where goods = dim of the projection of the solution
space of a2a3*M + D6(N) = 0 onto M-coordinates (canonical rank-nullity:
goods = nulldim_total - kerdim_C(m+1)).

Run:  python3 scripts/cas/test_N6_O1.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N6_O1 import goods_dim, nulldim_total


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("nulldim_total(1)=5", nulldim_total(1) == 5)
    ok &= _check("nulldim_total(2)=8", nulldim_total(2) == 8)
    ok &= _check("nulldim_total(6)=41", nulldim_total(6) == 41)
    ok &= _check("goods_dim(1)=0", goods_dim(1) == 0)
    ok &= _check("goods_dim(5)=0", goods_dim(5) == 0)
    ok &= _check("goods_dim(6)=1", goods_dim(6) == 1)
    print("test_N6_O1 OK" if ok else "test_N6_O1 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
