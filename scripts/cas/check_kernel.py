"""Check kernel: five-variable kernel + descent B^D = K (Theorem C).

Five-variable subproblem of the adjacent-quadratic shift at N = 5.
With x = a_3, y = a_2, z = a_1, p = a_4, q = a_5::

    B = k[x, y, z, p, q],  D(x) = pq, D(y) = px, D(z) = xy, D(p) = D(q) = 0,
    R = k[p, q, J_1, J_2], J_1 = 2pz - y^2, J_2 = 2qy - x^2.

With x = a_3, y = a_2, z = a_1, p = a_4, q = a_5::

    B = k[x, y, z, p, q],  D(x) = pq, D(y) = px, D(z) = xy, D(p) = D(q) = 0,
    R = k[p, q, J_1, J_2], J_1 = 2pz - y^2, J_2 = 2qy - x^2.

Slice: t = x/(pq), Y = y - x^2/(2q).

This script (SymPy-only + stdlib) asserts:
  1. D-invariance of p, q, J_1, J_2 via check_A
     (sys.path-insert of scripts/cas; from check_A import apply_D,
     verify_D with signature verify_D(poly, vars, N)).
  2. Algebraic independence of p, q, J_1, J_2 via an explicit Jacobian
     minor equal to 4*a_4*a_5 (nonzero over any characteristic-zero
     field; the scalar 4 is recorded so the char != 2 assumption is
     explicit).
  3. Slice identities: s = x/(pq) satisfies D(s) = 1, and the
     reconstruction identities expressing x, y, z over R_{pq}[s],
     which carry the localized kernel B_{pq}^D = R_{pq}.
  4. Specialization-independence spot checks: the monomials in
     (q, -y^2, 2qy-x^2) resp. (p, 2pz-y^2, -x^2) of total degree <= 5
     are linearly independent (finite certificate for the contraction
     lemma used in the descent).
  5. Divisibility identities: contraction instances
     (J_1 + y^2)/p = 2z, (J_2 + x^2... ) etc., plus the negative
     checks p does not divide J_1, J_2, q in B (one-variable
     polynomial division with nonzero remainder), i.e. denominators
     genuinely obstruct descent of e.g. J_1/p.

Run:
    python3 scripts/cas/check_kernel.py  # log: data/kernel.log
Prints PASS/FAIL per check plus a final `check_kernel OK` (exit 0/1).
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


def _check_generators():
    """D-invariance of the four kernel generators (N = 5)."""
    from sympy import symbols

    ok = True
    N = 5
    a = symbols("a_0:6")
    a0, a1, a2, a3, a4, a5 = a
    p, q = a4, a5
    J1 = 2 * a1 * a4 - a2**2
    J2 = 2 * a2 * a5 - a3**2
    ok &= _check("D(a_4)=0", apply_D(p, a, N) == 0)
    ok &= _check("D(a_5)=0", apply_D(q, a, N) == 0)
    ok &= _check("D(2a1a4-a2^2)=0", apply_D(J1, a, N) == 0)
    ok &= _check("D(2a2a5-a3^2)=0", apply_D(J2, a, N) == 0)
    ok &= _check("verify_D(p)", verify_D(p, a, N) is True)
    ok &= _check("verify_D(q)", verify_D(q, a, N) is True)
    ok &= _check("verify_D(J_1)", verify_D(J1, a, N) is True)
    ok &= _check("verify_D(J_2)", verify_D(J2, a, N) is True)
    # Five-variable derivation table in (x, y, z, p, q) coordinates.
    x, y, z = a3, a2, a1
    ok &= _check("D(x)=pq", apply_D(x, a, N) == p * q)
    ok &= _check("D(y)=px", apply_D(y, a, N) == p * x)
    ok &= _check("D(z)=xy", apply_D(z, a, N) == x * y)
    return ok


def _check_jacobian():
    """Algebraic independence of p, q, J_1, J_2 via an explicit minor."""
    from sympy import Matrix, symbols

    ok = True
    a = symbols("a_0:6")
    a0, a1, a2, a3, a4, a5 = a
    gens = [a4, a5, 2 * a1 * a4 - a2**2, 2 * a2 * a5 - a3**2]
    cols = [a1, a2, a4, a5]
    M = Matrix([[g.diff(c) for c in cols] for g in gens])
    ok &= _check("Jacobian 4x4 minor = 4*a_4*a_5", M.det() == 4 * a4 * a5)
    ok &= _check("minor is a nonzero polynomial", M.det() != 0)
    # Generically full rank: evaluate at (a1..a5) = (1, 2, 3, 4, 5).
    full = Matrix(
        [[g.diff(c) for c in a[1:]] for g in gens]
    ).subs(dict(zip(a[1:], (1, 2, 3, 4, 5))))
    ok &= _check("Jacobian rank 4 at sample point", full.rank() == 4)
    return ok


def _check_slice():
    """Local slice s = x/(pq): D(s) = 1 + reconstruction over R_{pq}[s]."""
    from sympy import symbols

    ok = True
    N = 5
    a = symbols("a_0:6")
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    J1 = 2 * p * z - y**2
    J2 = 2 * q * y - x**2
    s = x / (p * q)
    ok &= _check("D(s)=1 for s=x/(pq)", _is_zero(apply_D(s, a, N) - 1))
    ok &= _check("s is not invariant", verify_D(s, a, N) is False)
    Y = J2 / (2 * q)  # = y - x^2/(2q)
    Z = (J1 + Y**2) / (2 * p)
    ok &= _check("Y=y-x^2/(2q)", _is_zero(Y - (y - x**2 / (2 * q))))
    ok &= _check("D(Y)=0", _is_zero(apply_D(Y, a, N)))
    ok &= _check("D(Z)=0", _is_zero(apply_D(Z, a, N)))
    ok &= _check("2pZ-Y^2=J_1", _is_zero(2 * p * Z - Y**2 - J1))
    # Reconstruction: x, y, z as elements of R_{pq}[s].
    ok &= _check("x=pqs", _is_zero(x - p * q * s))
    ok &= _check("y=Y+p^2qs^2/2", _is_zero(y - (Y + p**2 * q * s**2 / 2)))
    ok &= _check(
        "z=Z+pqYs^2/2+p^3q^2s^4/8",
        _is_zero(z - (Z + p * q * Y * s**2 / 2 + p**3 * q**2 * s**4 / 8)),
    )
    return ok


def _monomials(vars3, deg):
    """All monomials in three variables of total degree <= deg."""
    from sympy import expand

    u, v, w = vars3
    out = []
    for i in range(deg + 1):
        for j in range(deg + 1 - i):
            for k in range(deg + 1 - i - j):
                out.append(expand(u**i * v**j * w**k))
    return out


def _independence_rank(substituted):
    """Rank of the coefficient matrix of substituted monomials."""
    from sympy import Matrix, Poly

    syms = set()
    for p in substituted:
        syms |= p.free_symbols
    syms = sorted(syms, key=lambda s: s.name)
    rows = []
    mon_index = {}
    for p in substituted:
        poly = Poly(p, *syms)
        row = {}
        for mon, coeff in poly.as_dict().items():
            if mon not in mon_index:
                mon_index[mon] = len(mon_index)
            row[mon_index[mon]] = coeff
        rows.append(row)
    ncols = len(mon_index)
    mat = [[0] * ncols for _ in rows]
    for i, row in enumerate(rows):
        for j, c in row.items():
            mat[i][j] = c
    return Matrix(mat).rank(), len(substituted), ncols


def _check_specialization(deg=5):
    """Finite independence certificates for the two contraction maps."""
    from sympy import expand, symbols

    ok = True
    y, x, z, q = symbols("y x z q")
    # Map alpha: k[q,U,V] -> k[x,y,z,q], (q,U,V) |-> (q,-y^2,2qy-x^2).
    U, V = symbols("U V")
    src = _monomials((q, U, V), deg)
    alpha = [expand(m.subs({U: -y**2, V: 2 * q * y - x**2})) for m in src]
    r, n, _ = _independence_rank(alpha)
    ok &= _check(
        "alpha independent through deg %d (%d monomials, rank %d)"
        % (deg, n, r),
        r == n,
    )
    # Map beta: k[p,U,V] -> k[x,y,z,p], (p,U,V) |-> (p,2pz-y^2,-x^2).
    p = symbols("p")
    src2 = _monomials((p, U, V), deg)
    beta = [expand(m.subs({U: 2 * p * z - y**2, V: -x**2})) for m in src2]
    r2, n2, _ = _independence_rank(beta)
    ok &= _check(
        "beta independent through deg %d (%d monomials, rank %d)"
        % (deg, n2, r2),
        r2 == n2,
    )
    return ok


def _check_divisibility():
    """Contraction instances: divisibility and genuine obstructions."""
    from sympy import Poly, symbols

    ok = True
    a = symbols("a_0:6")
    a0, a1, a2, a3, a4, a5 = a
    x, y, z, p, q = a3, a2, a1, a4, a5
    J1 = 2 * p * z - y**2
    J2 = 2 * q * y - x**2

    def divides(f, var):
        quo, rem = Poly(f, var).div(Poly(var, var))
        return rem.is_zero, quo.as_expr(), rem.as_expr()

    # Positive instances: reduction mod p / mod q.
    ok &= _check("J_1 mod p = -y^2", _is_zero(J1.subs(p, 0) + y**2))
    ok &= _check("J_2 mod q = -x^2", _is_zero(J2.subs(q, 0) + x**2))
    dp, qp_, _ = divides(J1 + y**2, p)
    ok &= _check("(J_1+y^2)/p=2z in B", dp and _is_zero(qp_ - 2 * z))
    dq, qq_, _ = divides(J2 + x**2, q)
    ok &= _check("(J_2+x^2)/q=2y in B", dq and _is_zero(qq_ - 2 * y))
    # Negative instances: p, q are prime to the other generators in B.
    for name, f, var in (
        ("p does not divide J_1", J1, p),
        ("p does not divide J_2", J2, p),
        ("p does not divide q", q, p),
        ("q does not divide J_1", J1, q),
        ("q does not divide J_2", J2, q),
        ("q does not divide p", p, q),
    ):
        rem_zero, _, _ = divides(f, var)
        ok &= _check(name, not rem_zero)
    # Denominator genuinely obstructs: J_1/p is not a polynomial.
    ok &= _check(
        "J_1/p not in B (remainder -y^2)",
        _is_zero(Poly(J1, p).div(Poly(p, p))[1].as_expr() + y**2),
    )
    # A sample invariant descends with a = b = 0.
    N = 5
    f = J1**2 + p * q * J2
    ok &= _check("sample J_1^2+pqJ_2 invariant", verify_D(f, a, N) is True)
    return ok


def main():
    ok = True
    ok &= _check_generators()
    ok &= _check_jacobian()
    ok &= _check_slice()
    ok &= _check_specialization()
    ok &= _check_divisibility()
    print("check_kernel OK" if ok else "check_kernel FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
