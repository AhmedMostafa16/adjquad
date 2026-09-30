"""Check slice: local slice s with D(s) in K nonzero + localized presentation.

Uses the shared generator definitions (no redefinition)::

    B = k[x, y, z, p, q],  x = a_3, y = a_2, z = a_1, p = a_4, q = a_5,
    D(x) = pq, D(y) = px, D(z) = xy, D(p) = D(q) = 0,
    J_1 = 2pz - y^2, J_2 = 2qy - x^2, R = k[p, q, J_1, J_2] subset K = B^D.

Produces (this task's scope only):
  1. Slice certificate: s = x/(pq) satisfies D(s) = 1, hence D(s) is a
     nonzero element of K (1 lies in every k-subalgebra, in particular
     1 in R subset K), while s itself is not invariant.
  2. Localized presentation check: B_{pq} = R_{pq}[s] via the explicit
     intermediaries Y = J_2/(2q), Z = (J_1 + Y^2)/(2p) (both invariant)
     and the reconstruction identities for x, y, z, with denominators
     verified to be powers of pq only.

Out of scope (explicitly NOT asserted here): the F_0-localized form
A_{pq}^{D_5} = K_{pq}[F_0] and any global generation claim A^D = K[F_0];
F_0 is constructed in the invariant section and
global generation stays Conditional on E. This script checks only the
slice mechanism that makes such localized presentations possible.

SymPy-only (+ stdlib). check_A imported via sys.path-insert of
scripts/cas (apply_D / verify_D with signature verify_D(poly, vars, N)).

Run:
    python3 scripts/cas/check_slice.py  # log: data/slice.log
Prints PASS/FAIL per check plus a final `check_slice OK` (exit 0/1).
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


def _denom_is_pq_power(expr, p, q, xz_vars):
    """True iff expr, in lowest terms, has denominator c*p**a*q**b."""
    from sympy import Poly, cancel

    _, denom = cancel(expr).as_numer_denom()
    poly = Poly(denom, *(list(xz_vars) + [p, q]))
    if poly is None:
        return False
    items = list(poly.as_dict().items())
    if len(items) != 1:
        return False
    mon, _coeff = items[0]
    nx = len(xz_vars)
    if any(mon[i] != 0 for i in range(nx)):
        return False
    return True


def _check_derivation_table(a, N):
    """Five-variable D-table reused verbatim from check_A (no redefinition)."""
    ok = True
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    ok &= _check("D(x)=pq", apply_D(x, a, N) == p * q)
    ok &= _check("D(y)=px", apply_D(y, a, N) == p * x)
    ok &= _check("D(z)=xy", apply_D(z, a, N) == x * y)
    ok &= _check("D(p)=0", apply_D(p, a, N) == 0)
    ok &= _check("D(q)=0", apply_D(q, a, N) == 0)
    return ok


def _check_kernel_gens(a, N):
    """J_1, J_2 invariant (exact forms verbatim from check_A report)."""
    ok = True
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    J1 = 2 * p * z - y**2
    J2 = 2 * q * y - x**2
    ok &= _check("D(J_1)=0", apply_D(J1, a, N) == 0)
    ok &= _check("D(J_2)=0", apply_D(J2, a, N) == 0)
    ok &= _check("verify_D(J_1)", verify_D(J1, a, N) is True)
    ok &= _check("verify_D(J_2)", verify_D(J2, a, N) is True)
    return ok, J1, J2


def _check_slice(a, N, J1, J2):
    """Slice s = x/(pq): D(s) = 1 is a nonzero element of K."""
    ok = True
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    s = x / (p * q)
    Ds = apply_D(s, a, N)
    ok &= _check("D(s)=1 for s=x/(pq)", _is_zero(Ds - 1))
    ok &= _check("D(s) nonzero", not _is_zero(Ds))
    ok &= _check("D(s) in K (verify_D(D(s)))", verify_D(Ds, a, N) is True)
    ok &= _check("1 in R subset K (constants invariant)", verify_D(1, a, N) is True)
    ok &= _check("s itself not invariant", verify_D(s, a, N) is False)
    return ok, s


def _check_localized_presentation(a, N, J1, J2, s):
    """B_{pq} = R_{pq}[s]: invariant intermediaries + reconstruction."""
    ok = True
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    xz = (x, y, z)
    Y = J2 / (2 * q)
    Z = (J1 + Y**2) / (2 * p)
    ok &= _check("D(Y)=0", _is_zero(apply_D(Y, a, N)))
    ok &= _check("D(Z)=0", _is_zero(apply_D(Z, a, N)))
    ok &= _check("Y=y-x^2/(2q)", _is_zero(Y - (y - x**2 / (2 * q))))
    # Denominators of the slice data involve only pq.
    ok &= _check("denom(s) is a pq-power", _denom_is_pq_power(s, p, q, xz))
    ok &= _check("denom(Y) is a pq-power", _denom_is_pq_power(Y, p, q, xz))
    ok &= _check("denom(Z) is a pq-power", _denom_is_pq_power(Z, p, q, xz))
    # Reconstruction: x, y, z as elements of R_{pq}[s].
    rx = p * q * s
    ry = Y + p**2 * q * s**2 / 2
    rz = Z + p * q * Y * s**2 / 2 + p**3 * q**2 * s**4 / 8
    ok &= _check("x=pqs", _is_zero(x - rx))
    ok &= _check("y=Y+p^2qs^2/2", _is_zero(y - ry))
    ok &= _check(
        "z=Z+pqYs^2/2+p^3q^2s^4/8",
        _is_zero(z - rz),
    )
    # The y/z right-hand sides, with Y/Z unfolded to J_1/J_2, still only
    # involve R-generators, s, and pq-denominators: membership in R_{pq}[s].
    Yj = J2 / (2 * q)
    Zj = (J1 + Yj**2) / (2 * p)
    ry_j = Yj + p**2 * q * s**2 / 2
    rz_j = Zj + p * q * Yj * s**2 / 2 + p**3 * q**2 * s**4 / 8
    ok &= _check("y-RHS in R_{pq}[s]", _is_zero(y - ry_j))
    ok &= _check("z-RHS in R_{pq}[s]", _is_zero(z - rz_j))
    for name, rhs in (("x-RHS", rx), ("y-RHS", ry_j), ("z-RHS", rz_j)):
        # s here is the rational expression x/(pq), so each right-hand
        # side is a rational function of the a-variables; its denominator
        # in lowest terms must be a power of pq for R_{pq}[s] membership.
        ok &= _check(
            "denom(%s) is a pq-power" % name,
            _denom_is_pq_power(rhs, p, q, xz),
        )
    # s adjoined: eliminating s recovers the kernel relation 2qY - J_2 = 0.
    ok &= _check(
        "slice eliminates to 2qY-J_2=0",
        _is_zero(2 * q * Y - J2),
    )
    ok &= _check(
        "slice eliminates to 2pZ-Y^2-J_1=0",
        _is_zero(2 * p * Z - Y**2 - J1),
    )
    return ok


def main():
    from sympy import symbols

    ok = True
    N = 5
    a = symbols("a_0:6")
    ok &= _check_derivation_table(a, N)
    step, J1, J2 = _check_kernel_gens(a, N)
    ok &= step
    step, s = _check_slice(a, N, J1, J2)
    ok &= step
    ok &= _check_localized_presentation(a, N, J1, J2, s)
    print("check_slice OK" if ok else "check_slice FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
