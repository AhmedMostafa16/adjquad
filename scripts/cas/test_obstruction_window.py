"""Oracle test for obstruction_window (TDD: written before the module)."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from obstruction_window import birth_window


N5 = [(1, 0), (1, 0), (6, 0), (4, 0), (14, 1)]


def _check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("N5 window == (16, 27)", birth_window(N5, 8) == (16, 27))
    lo, hi = birth_window(N5, 8)
    ok &= _check("H(24,2) strictly inside", lo <= 24 <= hi and lo < 24 < hi + 1
                 and (lo, hi) == (16, 27))
    print("test_obstruction_window OK" if ok else "test_obstruction_window FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
