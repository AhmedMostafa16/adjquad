"""Oracle test for s5_vs_s6_table (TDD: written before the module)."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from s5_vs_s6_table import coin_count, first_deviation


def _check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def main():
    ok = True
    ok &= _check("s5(14)==55", coin_count(14, [1, 1, 6, 4, 14]) == 55)
    ok &= _check("s5(24)==212", coin_count(24, [1, 1, 6, 4, 14]) == 212)
    ok &= _check("s6(24)==213", coin_count(24, [1, 1, 6, 4, 14, 24]) == 213)
    ok &= _check("s6 matches check_s6.s6 on 0..40",
                 all(coin_count(w, [1, 1, 6, 4, 14, 24]) == __import__("check_s6").s6(w)
                     for w in range(41)))
    ok &= _check("first deviation is w=24", first_deviation() == 24)
    print("test_s5_vs_s6_table OK" if ok else "test_s5_vs_s6_table FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
