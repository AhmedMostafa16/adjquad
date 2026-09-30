"""Check N=6 a0-top generator F0_6 (Phase 6): the missing top invariant.

A6 = k[a0..a6], D6(a0) = a1a2 (others as in check_N6_kernel.py).
With c6 = a5^2*a6^4 (the B-level slice denominator), the a0-denominator
is c6^2 = a5^4*a6^8 (found by elimination: c6, c6*a5, c6*a6 admit NO
G' with D6(G') = -c'*a1a2; c6^2 is the first that does -- the same
squaring pattern as N=5, where the B-slice denominator a4*a5^2 squares
to c = p^2*q^4). F0_6 = c6^2*a0 + G' with the 12-term G' below
(rational reconstruction + exact SageMath restricted solve,
/tmp/opencode/f0_6_restricted.py) satisfies D6(F0_6) = 0, has uniform
Fibonacci weight 25 (wt(a0) = 13), and a0-coefficient exactly c6^2.

This script (SymPy-only + stdlib) asserts D6(F0_6) = 0, the a0-form,
uniform weight 25, and ordinary degree 13 -- all exact over QQ.
Global A6-generation stays Open (needs its own saturation, Phase 7+).

Run:
    python3 scripts/cas/check_N6_F0.py  # log: data/n6/F0.log
Prints PASS/FAIL per check plus a final `check_N6_F0 OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402

WT = [13, 8, 5, 3, 2, 1, 1]  # a0..a6 (Fibonacci: wt(a0) = wt(a1)+wt(a2))

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def _vars():
    from sympy import symbols
    return symbols("a_0:7")


def _F0_6(a):
    from sympy import Rational
    a0, a1, a2, a3, a4, a5, a6 = a
    c6sq = a5**4 * a6**8
    Gp = (Rational(-1, 1) * a1 * a2 * a4 * a5**3 * a6**7
          + Rational(1, 3) * a1 * a3 * a4**3 * a5**2 * a6**6
          + Rational(-1, 15) * a1 * a4**5 * a5**2 * a6**5
          + Rational(1, 2) * a2**2 * a3 * a4**2 * a5**2 * a6**6
          + Rational(-1, 8) * a2**2 * a4**4 * a5**2 * a6**5
          + Rational(-1, 3) * a2 * a3**2 * a4**4 * a5 * a6**5
          + Rational(59, 360) * a2 * a3 * a4**6 * a5 * a6**4
          + Rational(-59, 2880) * a2 * a4**8 * a5 * a6**3
          + Rational(1, 18) * a3**3 * a4**6 * a6**4
          + Rational(-119, 2880) * a3**2 * a4**8 * a6**3
          + Rational(33, 3200) * a3 * a4**10 * a6**2
          + Rational(-11, 12800) * a4**12 * a6)
    return c6sq * a0 + Gp, c6sq, Gp


def _term_weight(term, a):
    from sympy import Poly
    exps = Poly(term, *a).as_dict()
    return {sum(e * w for e, w in zip(ex, WT)) for ex in exps}


def F0_6_invariant():
    from sympy import expand
    a = _vars()
    F, _, _ = _F0_6(a)
    return expand(apply_D(F, a, 6)) == 0


def F0_6_a0coeff_is_c6sq():
    from sympy import Poly, expand
    a = _vars()
    F, c6sq, _ = _F0_6(a)
    return expand(Poly(F, a[0]).nth(1) - c6sq) == 0


def F0_6_weight():
    from sympy import Poly
    a = _vars()
    F, _, _ = _F0_6(a)
    wts = set()
    for ex in Poly(F, *a).as_dict():
        wts.add(sum(e * w for e, w in zip(ex, WT)))
    return wts.pop() if len(wts) == 1 else -1


def main():
    from sympy import Poly, expand
    ok = True
    N = 6
    a = _vars()
    F, c6sq, Gp = _F0_6(a)
    ok &= check("D6(F0_6)=0", verify_D(F, a, N) is True)
    ok &= check("D6(F0_6)=0 (direct)", F0_6_invariant() is True)
    ok &= check("a0-coefficient is c6^2", F0_6_a0coeff_is_c6sq() is True)
    ok &= check("G' is a0-free", a[0] not in Gp.free_symbols)
    ok &= check("uniform Fibonacci weight 25", F0_6_weight() == 25)
    degs = sorted(Poly(g, *a).total_degree()
                  for g in Poly(F, *a).as_expr().args)
    ok &= check("ordinary degree 13 (max term degree)",
                Poly(F, *a).total_degree() == 13)
    nterms = len(Poly(F, *a).as_dict())
    ok &= check("13 terms (c6^2*a0 + 12)", nterms == 13)
    _ = degs
    for ln in log:
        print(ln)
    print("check_N6_F0 OK" if ok else "check_N6_F0 FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/F0.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N6_F0 OK" if ok
                       else "check_N6_F0 FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
