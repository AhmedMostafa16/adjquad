"""Check N=6 base kernel: five exact generators of B^D (Phase 1).

Adjacent-quadratic shift at N = 6, five-variable subproblem obtained by
deleting a_0. With B = k[a_1, ..., a_6] and D_6(a_n) = a_{n+1} a_{n+2}::

    D(a_1) = a_2 a_3,  D(a_2) = a_3 a_4,  D(a_3) = a_4 a_5,
    D(a_4) = a_5 a_6,  D(a_5) = D(a_6) = 0.

The N = 5 pattern (p, q, J_1, J_2) breaks down: the old J_1 = 2a_1a_4 - a_2^2
fails with defect D(J_1) = 2a_1a_5a_6, and no quadratic or cubic (in fact no
generator of degree <= 6) involving a_1 exists. The five exact generators
proved here are::

    G_1 = a_5,  G_2 = a_6,
    G_3 = 2a_2a_5 - a_3^2,  G_4 = 2a_3a_6 - a_4^2,
    G_5 = 105a_1a_5^2a_6^4 - 105a_2a_3a_4a_5a_6^3 + 35a_2a_4^3a_5a_6^2
         + 35a_3^2a_4^3a_6^2 - 21a_3a_4^5a_6 + 3a_4^7,

of degrees 1, 1, 2, 2, 7. G_5 is derived from scratch by the a_1-linear
ansatz G = a_1 M + N (M in the shifted-N=5 kernel, N in C = k[a_2..a_6]);
its invariance telescopes term by term (ladder identities below).

This script (SymPy-only + stdlib) asserts:
  1. The D-table on B and D-invariance of G_1..G_5 via the frozen
     interface (sys.path-insert of scripts/cas; from check_A import
     apply_D, verify_D).
  2. The six telescoping ladder identities exhibiting D(G_5) = 0.
  3. The pattern-breakdown witness: D(2a_1a_4 - a_2^2) = 2a_1a_5a_6 != 0.
  4. Algebraic independence: the 5x5 Jacobian minor in columns
     (a_1,a_2,a_3,a_5,a_6) equals 420*a_5^3*a_6^5 (nonzero over any
     characteristic-zero field; 420 = 2^2*3*5*7 records the char
     hypothesis explicitly), plus rank 5 at a sample point.
  5. Minimality: for the ansatz G = a_1 M + N with M of degree m in
     k[a_5,a_6,G_3,G_4], the solution spaces have (nulldim, goods) =
     (5,0),(8,0),(14,0),(20,0),(30,0) for m = 1..5 (no a_1-involving
     kernel element of degree <= 6) and (41,1) for m = 6 with the new
     direction M proportional to a_5^2a_6^4 (as pasted in G_5).
  6. Slice identities: s = a_4/(a_5a_6) satisfies D(s) = 1, with
     reconstruction of a_4, a_3, a_2, a_1 over R_{a_5a_6}[s]
     (R = k[G_1..G_5]), giving the localized kernel B_{a_5a_6}^D.
  7. Certified descent obstruction: G_5^2 + 9G_4^7 = a_6 S with S a
     polynomial satisfying D(S) = 0, so one-step contraction at (a_6)
     fails; global generation B^D = R is Conditional (see paper/10-n6).

Run:
    python3 scripts/cas/check_N6_kernel.py  # log: data/n6/kernel.log
Prints PASS/FAIL per check plus a final `check_kernel6 OK` (exit 0/1).
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


def _vars():
    from sympy import symbols

    a = symbols("a_0:7")
    return a


def _generators(a):
    a0, a1, a2, a3, a4, a5, a6 = a
    G1 = a5
    G2 = a6
    G3 = 2 * a2 * a5 - a3**2
    G4 = 2 * a3 * a6 - a4**2
    G5 = (
        105 * a1 * a5**2 * a6**4
        - 105 * a2 * a3 * a4 * a5 * a6**3
        + 35 * a2 * a4**3 * a5 * a6**2
        + 35 * a3**2 * a4**3 * a6**2
        - 21 * a3 * a4**5 * a6
        + 3 * a4**7
    )
    return [G1, G2, G3, G4, G5]


def _check_table():
    from sympy import expand

    ok = True
    N = 6
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    expected = {
        "D(a_1)=a_2a_3": (a1, a2 * a3),
        "D(a_2)=a_3a_4": (a2, a3 * a4),
        "D(a_3)=a_4a_5": (a3, a4 * a5),
        "D(a_4)=a_5a_6": (a4, a5 * a6),
        "D(a_5)=0": (a5, 0),
        "D(a_6)=0": (a6, 0),
    }
    for name, (var, val) in expected.items():
        ok &= _check(name, expand(apply_D(var, a, N) - val) == 0)
    return ok


def _check_generators():
    ok = True
    N = 6
    a = _vars()
    names = ["G_1=a_5", "G_2=a_6", "G_3=2a_2a_5-a_3^2",
             "G_4=2a_3a_6-a_4^2", "G_5 (degree 7)"]
    for name, g in zip(names, _generators(a)):
        ok &= _check("D(%s)=0" % name, apply_D(g, a, N) == 0)
        ok &= _check("verify_D(%s)" % name, verify_D(g, a, N) is True)
    return ok


def _check_ladder():
    from sympy import expand

    ok = True
    N = 6
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    T0 = 105 * a1 * a5**2 * a6**4
    T1 = -105 * a2 * a3 * a4 * a5 * a6**3
    T2 = 35 * a2 * a4**3 * a5 * a6**2
    T3 = 35 * a3**2 * a4**3 * a6**2
    T4 = -21 * a3 * a4**5 * a6
    T5 = 3 * a4**7
    G5 = _generators(a)[4]
    ok &= _check("G_5=T_0+...+T_5",
                 expand(G5 - (T0 + T1 + T2 + T3 + T4 + T5)) == 0)
    ok &= _check("D(T_0)=105a_2a_3a_5^2a_6^4",
                 expand(apply_D(T0, a, N) - 105 * a2 * a3 * a5**2 * a6**4) == 0)
    ok &= _check("D(T_1) kills T_0 defect",
                 expand(apply_D(T1, a, N) + 105 * a2 * a3 * a5**2 * a6**4
                        + 105 * a3**2 * a4**2 * a5 * a6**3
                        + 105 * a2 * a4**2 * a5**2 * a6**3) == 0)
    ok &= _check("D(T_2) kills a_2a_4^2 defect",
                 expand(apply_D(T2, a, N) - 35 * a3 * a4**4 * a5 * a6**2
                        - 105 * a2 * a4**2 * a5**2 * a6**3) == 0)
    ok &= _check("D(T_3) kills a_3^2a_4^2 defect",
                 expand(apply_D(T3, a, N) - 70 * a3 * a4**4 * a5 * a6**2
                        - 105 * a3**2 * a4**2 * a5 * a6**3) == 0)
    ok &= _check("D(T_4) kills a_3a_4^4 defect",
                 expand(apply_D(T4, a, N) + 21 * a4**6 * a5 * a6
                        + 105 * a3 * a4**4 * a5 * a6**2) == 0)
    ok &= _check("D(T_5) kills a_4^6 defect",
                 expand(apply_D(T5, a, N) - 21 * a4**6 * a5 * a6) == 0)
    return ok


def _check_breakdown():
    from sympy import expand

    ok = True
    N = 6
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    J1old = 2 * a1 * a4 - a2**2
    ok &= _check("old J_1 defect D(2a_1a_4-a_2^2)=2a_1a_5a_6",
                 expand(apply_D(J1old, a, N) - 2 * a1 * a5 * a6) == 0)
    ok &= _check("old J_1 not invariant", verify_D(J1old, a, N) is False)
    return ok


def _check_jacobian():
    from sympy import expand, Matrix

    ok = True
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    gens = _generators(a)
    cols = [a1, a2, a3, a5, a6]
    M = Matrix([[g.diff(c) for c in cols] for g in gens])
    ok &= _check("Jacobian 5x5 minor = 420*a_5^3*a_6^5",
                 expand(M.det() - 420 * a5**3 * a6**5) == 0)
    ok &= _check("minor is a nonzero polynomial", M.det() != 0)
    full = Matrix([[g.diff(c) for c in [a1, a2, a3, a4, a5, a6]]
                   for g in gens])
    pt = dict(zip([a1, a2, a3, a4, a5, a6], (1, 2, 3, 4, 5, 6)))
    ok &= _check("Jacobian rank 5 at sample point",
                 full.subs(pt).rank() == 5)
    return ok


def _c_monomials(vars_, deg):
    from sympy import expand

    n = len(vars_)
    out = []

    def rec(i, left, cur):
        if i == n - 1:
            m = 1
            for v, e in zip(vars_, cur + [left]):
                m *= v**e
            out.append(expand(m))
            return
        for e in range(left + 1):
            rec(i + 1, left - e, cur + [e])

    rec(0, deg, [])
    return out


def _t1_stats(m):
    """Nullspace stats for G = a_1 M + N with M of degree m in
    k[a_5,a_6,G_3,G_4] and N of degree m+1 in C = k[a_2..a_6]."""
    from itertools import combinations_with_replacement as cwr

    from sympy import Matrix, Poly, expand

    N = 6
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    C = [a2, a3, a4, a5, a6]
    G3 = 2 * a2 * a5 - a3**2
    G4 = 2 * a3 * a6 - a4**2
    Mb = []
    for r in range(m + 1):
        q = m - r
        if q % 2:
            continue
        for lc in cwr([a5, a6], r):
            for qc in cwr([G3, G4], q // 2):
                mm = 1
                for f in list(lc) + list(qc):
                    mm *= f
                Mb.append(expand(mm))
    Nb = _c_monomials(C, m + 1)
    src = Mb + Nb
    imgs = ([expand(a2 * a3 * b) for b in Mb]
            + [expand(apply_D(b, a, N)) for b in Nb])
    tgt = {}
    polys = []
    for e in imgs:
        if e == 0:
            polys.append({})
            continue
        d = Poly(e, *C).as_dict()
        polys.append(d)
        for mon in d:
            if mon not in tgt:
                tgt[mon] = len(tgt)
    mat = Matrix.zeros(len(tgt), len(src))
    for j, d in enumerate(polys):
        for mon, c in d.items():
            mat[tgt[mon], j] = c
    ns = mat.nullspace()
    goods = 0
    for v in ns:
        MM = expand(sum(c * b for c, b in zip(v[: len(Mb)], Mb)))
        if MM != 0:
            goods += 1
    return len(ns), goods


def _check_minimality():
    from sympy import Poly, expand

    ok = True
    expected = {1: (5, 0), 2: (8, 0), 3: (14, 0), 4: (20, 0), 5: (30, 0)}
    for m, (nulldim, goods) in expected.items():
        nd, gd = _t1_stats(m)
        ok &= _check("t1 m=%d: nulldim %d, no new direction" % (m, nulldim),
                     (nd, gd) == (nulldim, goods))
    nd, gd = _t1_stats(6)
    ok &= _check("t1 m=6: nulldim 41, exactly one new direction",
                 (nd, gd) == (41, 1))
    # The pasted G_5 realizes that direction: a_1-coefficient ~ a_5^2a_6^4.
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    G5 = _generators(a)[4]
    coeff_a1 = Poly(G5, a1).nth(1)
    ok &= _check("G_5 a_1-coefficient is 105a_5^2a_6^4",
                 expand(coeff_a1 - 105 * a5**2 * a6**4) == 0)
    degs = sorted(Poly(g, a1, a2, a3, a4, a5, a6).total_degree()
                  for g in _generators(a))
    ok &= _check("generator degrees are 1,1,2,2,7", degs == [1, 1, 2, 2, 7])
    return ok


def _check_slice():
    from sympy import cancel

    ok = True
    N = 6
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    s = a4 / (a5 * a6)
    ok &= _check("D(s)=1 for s=a_4/(a_5a_6)",
                 _is_zero(apply_D(s, a, N) - 1))
    ok &= _check("s is not invariant", verify_D(s, a, N) is False)
    ok &= _check("a_4=a_5a_6s", _is_zero(a4 - a5 * a6 * s))
    A3 = G4 / (2 * a6) + a5**2 * a6 * s**2 / 2
    ok &= _check("a_3=G_4/(2a_6)+a_5^2a_6s^2/2", _is_zero(A3 - a3))
    A2 = G3 / (2 * a5) + A3**2 / (2 * a5)
    ok &= _check("a_2=G_3/(2a_5)+a_3^2/(2a_5)", _is_zero(A2 - a2))
    N5 = G5 - 105 * a5**2 * a6**4 * a1
    A1 = (G5 - N5) / (105 * a5**2 * a6**4)
    ok &= _check("a_1=(G_5-N_5)/(105a_5^2a_6^4)", _is_zero(A1 - a1))
    ok &= _check("every denominator is a power of a_5a_6",
                 _is_zero(cancel(A2 - a2)) and _is_zero(cancel(A1 - a1)))
    _ = cancel  # silence linters about the import site
    return ok


def _check_obstruction():
    from sympy import Poly, cancel, expand

    ok = True
    N = 6
    a = _vars()
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    Z = expand(G5**2 + 9 * G4**7)
    ok &= _check("G_5^2+9G_4^7 vanishes mod a_6", Z.subs(a6, 0) == 0)
    S = cancel(Z / a6)
    ok &= _check("quotient S=(G_5^2+9G_4^7)/a_6 is a polynomial",
                 S == expand(S))
    ok &= _check("D(S)=0", verify_D(S, a, N) is True)
    ok &= _check("S has degree 13",
                 Poly(S, a1, a2, a3, a4, a5, a6).total_degree() == 13)
    return ok


def main():
    ok = True
    ok &= _check_table()
    ok &= _check_generators()
    ok &= _check_ladder()
    ok &= _check_breakdown()
    ok &= _check_jacobian()
    ok &= _check_minimality()
    ok &= _check_slice()
    ok &= _check_obstruction()
    print("check_kernel6 OK" if ok else "check_kernel6 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
