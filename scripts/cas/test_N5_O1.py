"""Oracle test for check_N5_O1 (TDD: written before the module).

Oracle: the shift isomorphism (paper/10-n6.tex, eq:n6-Ckernel)
  phi : (k[a1..a5], D5) -> (C, D6), a_i |-> a_{i+1},
sends a1a2 |-> a2a3, K = k[p,q,J1,J2] -> k[a5,a6,G3,G4], c |-> c6.
Hence the N=5 system a1a2*M + D5(N) = 0 has IDENTICAL stats to the N=6
system of check_N6_O1.py: nulldims (5,8,14,20,30,41), goods (0,0,0,0,0,1).

Run:  python3 scripts/cas/test_N5_O1.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_N5_O1 import goods_dim, nulldim_total


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
    print("test_N5_O1 OK" if ok else "test_N5_O1 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
