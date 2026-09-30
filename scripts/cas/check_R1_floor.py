"""R1 floor certificate for N=5 q-side (exact).

R1 claims: every invariant F of W-degree m satisfies
    lambda_q(F) := min_j (v_q(H_j) - 4*j) >= -2*m.
The proof (paper, q-lemma section) is the multiplicity transfer:
assuming deficit lambda < 0, the C_k initial forms give
P(r_q) = P'(r_q) = ... = P^{(c-1)}(r_q) = 0 with c = #{0<=k<=m :
lambda+4k < 0}; minpoly(r_q) of exact degree 2 (char 0, separable)
forces 2*c <= m, whence lambda >= -2m. Sharp: H (m=2, lambda=-4),
F_46 (m=4, lambda=-8).

This script certifies the CAS-checkable identities (exact rational
arithmetic); the field-membership non-inclusion r_q not in L_q is a
parity proof in the paper (x-degree 7 odd vs even), and the
valuation-arithmetic transfer is pure algebra there.

Checks:
 1. r_q^2 identity: r_q^2 - (x^2)^7/(1225*p^4) == 0 exactly.
 2. minpoly evaluation + simplicity: m(r_q) == 0, m'(r_q) != 0
    with m(T) = T^2 - (x^2)^7/(1225*p^4).
 3. R1 floor on documented W-deficit profiles: H (deficits (-4,-4)
    at j=2,0) and F_46 (deficits all -8 at j=0,1,2,4).
 4. Combinatorial core scan: for m in 0..12 and every integer lambda,
    (lambda < -2*m) implies (2*count > m), where
    count = #{0<=k<=m : lambda+4k < 0}. This is the exact
    contrapositive used by the proof (count*2 <= m forces
    lambda >= -2m). The converse is FALSE in general (e.g. m=1,
    lambda=-2 gives count=1, 2 > 1: the multiplicity bound is
    strictly stronger than R1 there, forcing lambda >= 0).

Run:
    python3 scripts/cas/check_R1_floor.py  # log: data/R1_floor.log
Prints PASS/FAIL per check plus a final `check_R1_floor OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import symbols, expand, cancel, diff  # noqa: E402

x, p, T = symbols("x p T")

RQ = x**7/(35*p**2)
MINPOLY = T**2 - (x**2)**7/(1225*p**4)


def rq_square_identity():
    """r_q^2 - (x^2)^7/(1225*p^4) == 0."""
    return cancel(expand(RQ**2 - (x**2)**7/(1225*p**4))) == 0


def minpoly_eval_zero():
    """m(r_q) == 0."""
    return cancel(expand(MINPOLY.subs(T, RQ))) == 0


def minpoly_simple_root():
    """m'(r_q) = 2*r_q != 0 (separable; exact degree 2 given r_q not in L_q)."""
    d = diff(MINPOLY, T)
    return cancel(expand(d.subs(T, RQ))) == 2*RQ and RQ != 0


def r1_on_H():
    """H: W-degree 2, deficits (v_q(H_2)-8, v_q(H_0)-0) = (4-8, -4-0)."""
    deficits = [4 - 8, -4 - 0]
    return min(deficits) >= -2*2 and min(deficits) == -4


def r1_on_F46():
    """F_46: W-degree 4, v_q profile (-8,-4,0,8) at j=0,1,2,4."""
    vq = {0: -8, 1: -4, 2: 0, 4: 8}
    deficits = [vq[j] - 4*j for j in vq]
    return min(deficits) >= -2*4 and min(deficits) == -8


def combinatorial_core():
    """(lambda < -2*m) implies (2*count > m) for m in 0..12, all lambda."""
    for m in range(0, 13):
        for lam in range(-4*m - 3, 2):
            count = sum(1 for k in range(0, m + 1) if lam + 4*k < 0)
            if lam < -2*m and not (2*count > m):
                return False, (m, lam, count)
    return True, None


CHECKS = [
    ("rq_square_identity", rq_square_identity),
    ("minpoly_eval_zero", minpoly_eval_zero),
    ("minpoly_simple_root", minpoly_simple_root),
    ("r1_on_H", r1_on_H),
    ("r1_on_F46", r1_on_F46),
]


def main():
    ok = True
    for name, fn in CHECKS:
        try:
            passed = bool(fn())
        except Exception as exc:  # noqa: BLE001
            passed = False
            print("FAIL %s: %s" % (name, exc))
            ok = False
            continue
        print(("PASS " if passed else "FAIL ") + name)
        ok = ok and passed
    passed, witness = combinatorial_core()
    print(("PASS " if passed else "FAIL ") + "combinatorial_core"
          + ("" if passed else " at %s" % (witness,)))
    ok = ok and passed
    print("check_R1_floor " + ("OK" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
