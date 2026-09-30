"""Check N=6 saturation setup: per-divisor valuation data, residue fields, initials.

Status: Central theorem under verification. This script (SymPy-only +
stdlib) certifies ONLY finite setup identities for the two
residue-transcendence lemmas of the adjacent-quadratic shift at N = 6;
it does NOT certify either saturation inference itself
(v_5(H_j) >= 2j, v_6(H_j) >= 4j), which stays under verification in
``paper/10-n6.tex`` (Lemmas ``lem:n6-sat5``/``lem:n6-sat6``).

K/slice/c_6 reused verbatim from the Tasks 2-4 reports (no redefinition):
B = k[a_1, ..., a_6], C = k[a_2, ..., a_6],
D(a_1) = a_2a_3, D(a_2) = a_3a_4, D(a_3) = a_4a_5, D(a_4) = a_5a_6,
D(a_5) = D(a_6) = 0;
G_1 = a_5, G_2 = a_6, G_3 = 2a_2a_5 - a_3^2, G_4 = 2a_3a_6 - a_4^2,
G_5 = 105a_1a_5^2a_6^4 + N_5 with N_5 free of a_1;
C^D = k[a_5, a_6, G_3, G_4]; c_6 = a_5^2a_6^4;
W# = G_5/(105c_6) = a_1 + rho#, rho# = N_5/(105c_6) in C_{a_5a_6}.

This script asserts, with the a_5 and a_6 sides computed independently
(no symmetry argument in either direction):
  1. D-table + G_1..G_5 invariance..
  2. W# shape: a_1-coefficient of G_5 is 105c_6; N_5 free of a_1.
  3. Denominator exponents: c_6 = a_5^2a_6^4 has ord_5 2 (e_5) and
     ord_6 4 (e_6); the two exponents differ (asymmetry).
  4. a_5-side C-level specialization rows: G_3/G_4/N_5 mod a_5
     (residue-field generator computation for L_5); N_5 mod a_5 is the
     trinomial initial numerator (nonzero); exact pole order 0 for N_5.
  5. a_6-side C-level specialization rows: G_3/G_4/N_5 mod a_6
     (independent computation for L_6); N_5 mod a_6 is the monomial
     3a_4^7 (nonzero); exact pole order 0 for N_5.
  6. Residue-field setup independence per side: {a_6,-a_3^2,2a_3a_6-a_4^2}
     has Jacobian minor 4a_3a_4 != 0; {a_5,2a_2a_5-a_3^2,-a_4^2} has
     minor -4a_4a_5 != 0 (so each C-level specialization map is injective
     and each L is purely transcendental of degree 3).
  7. Slice initials: a_5s|_{a_5=0} = a_4/a_6 and a_6s|_{a_6=0} = a_4/a_5,
     both nonzero (exact pole order 1 of s at each divisor).
  8. Algebraicity witnesses for the obstacle remarks: t = a_3/a_6 with
     t^2 in L_5 and u = a_4/a_6 with u^2 in L_5(t) (two-step tower of
     degree at most 4 over L_5 containing the a_5 initial form);
     sbar_6 = a_4/a_5 with sbar_6^2 in L_6 (one quadratic step over L_6).
  9. R-level kernel witnesses (route blockers, not inferences):
     (G_5^2+9G_4^7)|_{a_6=0} = 0 with S = (G_5^2+9G_4^7)/a_6 polynomial,
     nonzero, D(S) = 0; REL5 formal nonzero vanishing on the a_5-side
     R-residues (so neither R-level specialization map is injective).

Out of scope (explicitly NOT asserted): the valuation bounds
v_5(H_j) >= 2j and v_6(H_j) >= 4j, any transcendence claim for the
initial forms over L_5/L_6, W#-degree induction, global generation,
Hilbert series. No parity shortcut, no slice-power computation, no
coordinate change, and no inference of generation from a single divisor
is used as proof here or in the tex section.

Run:
    python3 scripts/cas/check_N6_sat.py  # log: data/n6/sat.log
Prints PASS/FAIL per check plus a final `check_sat6 OK` (exit 0/1).
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

    return symbols("a_0:7")


def _generators(a):
    # Exact forms from check_A (do not redefine).
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


def _check_table(a, N):
    from sympy import expand

    ok = True
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


def _check_kernel_gens(a, N):
    ok = True
    names = ["G_1=a_5", "G_2=a_6", "G_3=2a_2a_5-a_3^2",
             "G_4=2a_3a_6-a_4^2", "G_5 (degree 7)"]
    for name, g in zip(names, _generators(a)):
        ok &= _check("D(%s)=0" % name, apply_D(g, a, N) == 0)
        ok &= _check("verify_D(%s)" % name, verify_D(g, a, N) is True)
    return ok


def _check_wshape(a):
    from sympy import Poly, expand

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    c6 = a5**2 * a6**4
    C6 = 105 * a5**2 * a6**4
    ok &= _check("c_6=a_5^2a_6^4", expand(c6 - a5**2 * a6**4) == 0)
    ok &= _check("D(c_6)=0", apply_D(c6, a, 6) == 0)
    coeff_a1 = Poly(G5, a1).nth(1)
    ok &= _check("G_5 a_1-coefficient is 105c_6",
                 expand(coeff_a1 - C6) == 0)
    N5 = expand(G5 - C6 * a1)
    ok &= _check("N_5=G_5-105c_6a_1 free of a_1",
                 Poly(N5, a1).degree() == 0 or _is_zero(Poly(N5, a1).nth(1)))
    ok &= _check("W# shape: G_5-105c_6a_1-N_5=0",
                 expand(G5 - C6 * a1 - N5) == 0)
    # Denominator exponents (asymmetric).
    ok &= _check("ord-a5-c_6-2", Poly(c6, a5).degree() == 2)
    ok &= _check("ord-a6-c_6-4", Poly(c6, a6).degree() == 4)
    ok &= _check("exponents differ (2 vs 4)", 2 != 4)
    return ok, N5


def _check_side5(a, N5):
    from sympy import Matrix, Poly, expand

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    # Specialization rows (computed on the a_5 side only).
    ok &= _check("G1-mod-a5-0", expand(G1.subs(a5, 0)) == 0)
    ok &= _check("G2-mod-a5-is-a6", expand(G2.subs(a5, 0) - a6) == 0)
    ok &= _check("G3-mod-a5-is--a3^2",
                 expand(G3.subs(a5, 0) - (-a3**2)) == 0)
    ok &= _check("G4-mod-a5-is-2a3a6-a4^2",
                 expand(G4.subs(a5, 0) - (2 * a3 * a6 - a4**2)) == 0)
    rp_num = (35 * a3**2 * a4**3 * a6**2 - 21 * a3 * a4**5 * a6
              + 3 * a4**7)
    N5p = expand(N5.subs(a5, 0))
    ok &= _check("N5-mod-a5-is-trinomial", expand(N5p - rp_num) == 0)
    ok &= _check("N5-mod-a5-nonzero", N5p != 0)
    ok &= _check("N5-mod-a5-has-3-terms",
                 len(Poly(rp_num, a3, a4, a6).terms()) == 3)
    ok &= _check("vp-N5-zero", Poly(N5, a5).nth(0) != 0)
    # Residues lie in k[a_3,a_4,a_6] (a_1, a_2, a_5 absent).
    for name, spec in (("G3", expand(G3.subs(a5, 0))),
                       ("G4", expand(G4.subs(a5, 0))),
                       ("N5", N5p)):
        ok &= _check("%s-mod-a5 in k[a3,a4,a6]" % name,
                     expand(spec - spec.subs({a1: 0, a2: 0, a5: 0})) == 0)
    # Setup independence: 3 generators, minor 4a_3a_4.
    det5 = expand(Matrix([a6, -a3**2, 2 * a3 * a6 - a4**2])
                  .jacobian([a6, a3, a4]).det())
    ok &= _check("L5-setup-minor-4a3a4", det5 - 4 * a3 * a4 == 0)
    ok &= _check("L5-setup-minor-nonzero", det5 != 0)
    return ok


def _check_side6(a, N5):
    from sympy import Matrix, Poly, expand

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    # Specialization rows (computed on the a_6 side only).
    ok &= _check("G2-mod-a6-0", expand(G2.subs(a6, 0)) == 0)
    ok &= _check("G1-mod-a6-is-a5", expand(G1.subs(a6, 0) - a5) == 0)
    ok &= _check("G3-mod-a6-is-2a2a5-a3^2",
                 expand(G3.subs(a6, 0) - (2 * a2 * a5 - a3**2)) == 0)
    ok &= _check("G4-mod-a6-is--a4^2",
                 expand(G4.subs(a6, 0) - (-a4**2)) == 0)
    rq_num = 3 * a4**7
    N5q = expand(N5.subs(a6, 0))
    ok &= _check("N5-mod-a6-is-monomial-3a4^7",
                 expand(N5q - rq_num) == 0)
    ok &= _check("N5-mod-a6-nonzero", N5q != 0)
    ok &= _check("N5-mod-a6-has-1-term",
                 len(Poly(rq_num, a4).terms()) == 1)
    ok &= _check("vq-N5-zero", Poly(N5, a6).nth(0) != 0)
    # Residues lie in k[a_2,a_3,a_4,a_5] (a_1, a_6 absent).
    for name, spec in (("G3", expand(G3.subs(a6, 0))),
                       ("G4", expand(G4.subs(a6, 0))),
                       ("N5", N5q)):
        ok &= _check("%s-mod-a6 in k[a2,a3,a4,a5]" % name,
                     expand(spec - spec.subs({a1: 0, a6: 0})) == 0)
    # Setup independence: 3 generators, minor -4a_4a_5.
    det6 = expand(Matrix([a5, 2 * a2 * a5 - a3**2, -a4**2])
                  .jacobian([a5, a2, a4]).det())
    ok &= _check("L6-setup-minor--4a4a5", det6 - (-4 * a4 * a5) == 0)
    ok &= _check("L6-setup-minor-nonzero", det6 != 0)
    return ok


def _check_slice_initials(a):
    from sympy import cancel

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    s = a4 / (a5 * a6)
    ok &= _check("D(s)=1 for s=a_4/(a_5a_6)",
                 _is_zero(apply_D(s, a, 6) - 1))
    ok &= _check("a5s-initial-is-a4/a6",
                 _is_zero(a5 * s - a4 / a6))
    ok &= _check("a5s-initial-nonzero", not _is_zero(a4 / a6))
    ok &= _check("a6s-initial-is-a4/a5",
                 _is_zero(a6 * s - a4 / a5))
    ok &= _check("a6s-initial-nonzero", not _is_zero(a4 / a5))
    ok &= _check("cancel-consistency", cancel(a5 * s - a4 / a6) == 0)
    return ok


def _check_obstacles(a, N5):
    from sympy import Poly, cancel, expand, symbols

    ok = True
    a0, a1, a2, a3, a4, a5, a6 = a
    G1, G2, G3, G4, G5 = _generators(a)
    # a_5-side tower: t = a_3/a_6, u = a_4/a_6 over L_5.
    Y2, Y3, Y4 = a6, -a3**2, 2 * a3 * a6 - a4**2
    t, u = a3 / a6, a4 / a6
    ok &= _check("t^2+Y3/Y2^2=0", cancel(t**2 + Y3 / Y2**2) == 0)
    ok &= _check("u^2-2t+Y4/Y2^2=0",
                 cancel(u**2 - 2 * t + Y4 / Y2**2) == 0)
    ok &= _check("t-nonzero", not _is_zero(t))
    ok &= _check("u-nonzero", not _is_zero(u))
    # a_6-side single step: sbar_6 = a_4/a_5 over L_6.
    y1, y4 = a5, -a4**2
    ok &= _check("sbar6^2+y4/y1^2=0",
                 cancel((a4 / a5)**2 + y4 / y1**2) == 0)
    # a_6-side R-level kernel witness (Lemma n6-obstruction, rechecked).
    Z = expand(G5**2 + 9 * G4**7)
    ok &= _check("Z-mod-a6-0", expand(Z.subs(a6, 0)) == 0)
    num, den = cancel(Z / a6).as_numer_denom()
    ok &= _check("S=(Z/a6) polynomial", den == 1)
    S = expand(num)
    ok &= _check("S-nonzero", S != 0)
    ok &= _check("D(S)=0", apply_D(S, a, 6) == 0)
    # a_5-side R-level kernel witness REL5 (formal nonzero, vanishes).
    Y2s, Y3s, Y4s, Y5s = symbols("Y2 Y3 Y4 Y5")
    REL5Y = (40000 * Y2s**14 * Y3s**7 + 193200 * Y2s**12 * Y3s**6 * Y4s**2
             + 325164 * Y2s**10 * Y3s**5 * Y4s**4
             + 236425 * Y2s**8 * Y3s**4 * Y4s**6
             + 88410 * Y2s**6 * Y3s**3 * Y4s**8
             + 840 * Y2s**6 * Y3s**3 * Y4s * Y5s**2
             + 17955 * Y2s**4 * Y3s**2 * Y4s**10
             + 770 * Y2s**4 * Y3s**2 * Y4s**3 * Y5s**2
             + 1890 * Y2s**2 * Y3s * Y4s**12
             + 210 * Y2s**2 * Y3s * Y4s**5 * Y5s**2
             + 81 * Y4s**14 + 18 * Y4s**7 * Y5s**2 + Y5s**4)
    ok &= _check("REL5-formal-nonzero",
                 len(Poly(REL5Y, Y2s, Y3s, Y4s, Y5s).terms()) == 13)
    ok &= _check("REL5-vanishes-on-a5-residues",
                 expand(REL5Y.subs({Y2s: a6, Y3s: -a3**2,
                                    Y4s: 2 * a3 * a6 - a4**2,
                                    Y5s: expand(N5.subs(a5, 0))})) == 0)
    return ok


def main():
    ok = True
    N = 6
    a = _vars()
    ok &= _check_table(a, N)
    ok &= _check_kernel_gens(a, N)
    step, N5 = _check_wshape(a)
    ok &= step
    ok &= _check_side5(a, N5)
    ok &= _check_side6(a, N5)
    ok &= _check_slice_initials(a)
    ok &= _check_obstacles(a, N5)
    print("check_sat6 OK" if ok else "check_sat6 FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
