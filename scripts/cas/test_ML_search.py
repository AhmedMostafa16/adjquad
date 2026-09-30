"""Oracle test for check_ML_search (TDD: written before the module).

Structural facts: D5 itself (quadratic triangular) lies in the ansatz
and preserves K; the preserving subspace is nonzero.

Run:  python3 scripts/cas/test_ML_search.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_ML_search import D5_in_ansatz, preserving_dim


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("D5 in triangular ansatz", D5_in_ansatz() is True)
    ok &= _check("preserving subspace nonzero", preserving_dim() >= 1)
    print("test_ML_search OK" if ok else "test_ML_search FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
