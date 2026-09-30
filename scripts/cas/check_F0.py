"""Check F_0: explicit N=5 invariant, degree 7, weight 14 + independence.

Theorem D (Established): the degree-7 polynomial invariant of the
adjacent-quadratic shift at N = 5 satisfies D_5(F_0) = 0 and is
algebraically independent of the K-generators via the Jacobian
criterion (characteristic-zero hypothesis).

Exact polynomial::

    F_0 = p^2q^4a_0 - pq^3xyz + (1/3)pq^2x^3z + (1/3)q^2x^3y^2
          - (1/5)qx^5y + (1/35)x^7,

with x = a_3, y = a_2, z = a_1, p = a_4, q = a_5
(i.e. in a-variables: a_4^2a_5^4a_0 - a_4a_5^3a_3a_2a_1
+ (1/3)a_4a_5^2a_3^3a_1 + (1/3)a_5^2a_3^3a_2^2
- (1/5)a_5a_3^5a_2 + (1/35)a_3^7).

K-generators reused verbatim from check_A (no redefinition):
p = a_4, q = a_5, J_1 = 2a_1a_4 - a_2^2, J_2 = 2a_2a_5 - a_3^2.

This script (SymPy-only + stdlib) asserts:
  1. D-invariance: verify_D(F_0) is True), plus the
     term-by-term D-table whose groups cancel to zero.
  2. Ordinary degree 7: total degree 7 and every monomial degree 7.
  3. Fibonacci weight 14: wt(a_0..a_5) = (8,5,3,2,1,1); every
     monomial has weight 14.
  4. Algebraic independence of p, q, J_1, J_2, F_0 via the explicit
     5x5 Jacobian minor in columns (a_0,a_1,a_2,a_4,a_5) equal to
     4*a_4^3*a_5^5 (nonzero over char 0; the scalar 4 records the
     char != 2 assumption; the denominators 3, 5, 35 in F_0 are
     likewise covered by the standing characteristic-zero
     hypothesis), plus generic rank 5 at a sample point, plus the
     triangular a_0-linearity spot check (F_0 = p^2q^4*a_0 + G_0
     with G_0 free of a_0).

Out of scope (explicitly NOT asserted here): global generation
A^D = K[F_0], minimality of F_0, saturation (statement E), and any
Hilbert-series claim. Those stay Conditional (on E) / Open for
later tasks; this script certifies only the invariant itself and
its independence.

Run:
    python3 scripts/cas/check_F0.py  # log: data/F0.log
Prints PASS/FAIL per check plus a final `check_F0 OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def _is_zero(expr):
    from sympy import cancel, expand

    if expand(expr) == 0:
        return True
    return cancel(expr) == 0


def build_F0(a):
    """Exact audited F_0 in the a-variables (no other form asserted)."""
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    return (
        p**2 * q**4 * a0
        - p * q**3 * x * y * z
        + p * q**2 * x**3 * z / 3
        + q**2 * x**3 * y**2 / 3
        - q * x**5 * y / 5
        + x**7 / 35
    )


def _check_invariance(a, N, F0):
    """D_5(F_0) = 0: whole-polynomial plus term-by-term D-table."""
    from sympy import Rational

    ok = True
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    ok &= _check("verify_D(F_0) is True", verify_D(F0, a, N) is True)
    ok &= _check("apply_D(F_0) == 0", apply_D(F0, a, N) == 0)
    # Term-by-term D-table (record, audited verification section):
    # D(x)=pq, D(y)=px, D(z)=xy, D(p)=D(q)=0, D(a_0)=zy (= a_1a_2).
    t1 = p**2 * q**4 * a0
    t2 = -p * q**3 * x * y * z
    t3 = p * q**2 * x**3 * z / 3
    t4 = q**2 * x**3 * y**2 / 3
    t5 = -q * x**5 * y / 5
    t6 = x**7 / 35
    ok &= _check("F_0 sums to its six terms", _is_zero(F0 - (t1 + t2 + t3 + t4 + t5 + t6)))
    ok &= _check("D(t1)=p^2q^4zy", _is_zero(apply_D(t1, a, N) - p**2 * q**4 * z * y))
    ok &= _check(
        "D(t2)=-p^2q^4yz-p^2q^3x^2z-pq^3x^2y^2",
        _is_zero(apply_D(t2, a, N) + p**2 * q**4 * y * z + p**2 * q**3 * x**2 * z + p * q**3 * x**2 * y**2),
    )
    ok &= _check(
        "D(t3)=p^2q^3x^2z+(1/3)pq^2x^4y",
        _is_zero(apply_D(t3, a, N) - p**2 * q**3 * x**2 * z - Rational(1, 3) * p * q**2 * x**4 * y),
    )
    ok &= _check(
        "D(t4)=pq^3x^2y^2+(2/3)pq^2x^4y",
        _is_zero(apply_D(t4, a, N) - p * q**3 * x**2 * y**2 - Rational(2, 3) * p * q**2 * x**4 * y),
    )
    ok &= _check(
        "D(t5)=-pq^2x^4y-(1/5)pqx^6",
        _is_zero(apply_D(t5, a, N) + p * q**2 * x**4 * y + Rational(1, 5) * p * q * x**6),
    )
    ok &= _check(
        "D(t6)=(1/5)pqx^6",
        _is_zero(apply_D(t6, a, N) - Rational(1, 5) * p * q * x**6),
    )
    # Cancellation groups (record table groupings).
    ok &= _check(
        "group p^2q^4zy cancels",
        _is_zero(apply_D(t1, a, N) + (-p**2 * q**4 * y * z)),
    )
    ok &= _check(
        "all six D-terms sum to 0",
        _is_zero(
            apply_D(t1, a, N)
            + apply_D(t2, a, N)
            + apply_D(t3, a, N)
            + apply_D(t4, a, N)
            + apply_D(t5, a, N)
            + apply_D(t6, a, N)
        ),
    )
    return ok


def _check_degree(a, F0):
    """Ordinary degree 7: total plus every monomial."""
    from sympy import Poly

    ok = True
    poly = Poly(F0, *a)
    ok &= _check("total ordinary degree 7", poly.total_degree() == 7)
    degs = sorted(sum(e) for e in poly.monoms())
    ok &= _check("six monomials present", len(degs) == 6)
    ok &= _check("every monomial has degree 7", all(d == 7 for d in degs))
    return ok


def _check_weight(a, F0):
    """Fibonacci weight 14 for every monomial."""
    from sympy import Poly

    ok = True
    wt = {a[0]: 8, a[1]: 5, a[2]: 3, a[3]: 2, a[4]: 1, a[5]: 1}
    weights = []
    for exps in Poly(F0, *a).monoms():
        weights.append(sum(e * wt[ai] for e, ai in zip(exps, a)))
    ok &= _check("every monomial has Fibonacci weight 14", all(w == 14 for w in weights))
    ok &= _check("weight list is [14]*6", weights == [14] * 6)
    return ok


def _check_jacobian(a, F0):
    """Independence of p, q, J_1, J_2, F_0 via an explicit minor."""
    from sympy import Matrix, expand

    ok = True
    a0, a1, a2, a3, a4, a5 = a
    J1 = 2 * a1 * a4 - a2**2
    J2 = 2 * a2 * a5 - a3**2
    gens = [a4, a5, J1, J2, F0]
    cols = [a0, a1, a2, a4, a5]
    M = Matrix([[g.diff(c) for c in cols] for g in gens])
    ok &= _check(
        "Jacobian 5x5 minor = 4*a_4^3*a_5^5",
        expand(M.det() - 4 * a4**3 * a5**5) == 0,
    )
    ok &= _check("minor is a nonzero polynomial", M.det() != 0)
    # Triangular spot check: F_0 linear in a_0, others free of a_0.
    ok &= _check(
        "dF_0/da_0 = p^2q^4",
        _is_zero(F0.diff(a0) - a4**2 * a5**4),
    )
    for name, g in (("p", a4), ("q", a5), ("J_1", J1), ("J_2", J2)):
        ok &= _check("%s free of a_0" % name, g.diff(a0) == 0)
    # Generically full rank: evaluate the 5x6 Jacobian at a sample point.
    full = Matrix([[g.diff(c) for c in a] for g in gens]).subs(
        dict(zip(a, (0, 1, 2, 3, 4, 5)))
    )
    ok &= _check("Jacobian rank 5 at sample point", full.rank() == 5)
    return ok


def _check_a0_linearity(a, N, F0):
    """F_0 = p^2q^4*a_0 + G_0 with G_0 in B = k[a_1..a_5]."""
    from sympy import Poly

    ok = True
    a0, a1, a2, a3, a4, a5 = a
    c = a4**2 * a5**4
    G0 = F0 - c * a0
    ok &= _check("G_0 free of a_0", Poly(G0, a0).degree() == 0)
    ok &= _check("G_0 lies in B (no a_0 symbols)", a0 not in G0.free_symbols)
    ok &= _check(
        "D-split cancels: D(c*a_0)+D(G_0)=0",
        _is_zero(apply_D(c * a0, a, N) + apply_D(G0, a, N)),
    )
    return ok


def main():
    from sympy import symbols

    ok = True
    N = 5
    a = symbols("a_0:6")
    F0 = build_F0(a)
    ok &= _check_invariance(a, N, F0)
    ok &= _check_degree(a, F0)
    ok &= _check_weight(a, F0)
    ok &= _check_jacobian(a, F0)
    ok &= _check_a0_linearity(a, N, F0)
    print("check_F0 OK" if ok else "check_F0 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
