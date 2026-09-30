"""Check p-lemma setup: valuation data, residue fields, initial forms.

Status: Central theorem under verification (Theorem E). This script
(SymPy-only + stdlib) certifies ONLY finite setup identities for the
p-adic residue-transcendence lemma of the adjacent-quadratic shift
at N = 5; it does NOT certify the saturation inference itself
(v_p(H_j) >= 2j), which stays under verification in
``paper/05a-plemma.tex`` (Lemma ``lem:plemma``).

K/F_0 reused from check_kernel (no redefinition):
x = a_3, y = a_2, z = a_1, p = a_4, q = a_5;
p = a_4, q = a_5, J_1 = 2a_1a_4 - a_2^2, J_2 = 2a_2a_5 - a_3^2;
D-table D(x) = pq, D(y) = px, D(z) = xy;
F_0 = p^2q^4a_0 - pq^3xyz + (1/3)pq^2x^3z + (1/3)q^2x^3y^2
      - (1/5)qx^5y + (1/35)x^7.

This script asserts:
  1. Specialization rows: J_1/J_2 mod p and mod q (the residue-field
     generator computations for L_p and L_q).
  2. Initial-form numerators: G_0 mod p (r_p numerator) and G_0
     mod q (r_q numerator), both nonzero (exact pole orders).
  3. Denominator exponents: c = p^2q^4 has ord_p 2 (e_p) and
     ord_q 4 (e_q).
  4. Residue-field setup independence: {q, y^2, 2qy-x^2, z} has
     Jacobian minor 4xy != 0 (so L_p is purely transcendental of
     degree 3 and z is transcendental over L_p); {p, 2pz-y^2, x^2}
     has 3x3 minor 4xy != 0 (L_q setup, purely transcendental
     degree 3).
  5. Algebraicity witnesses for the obstacle remark: y^2 and x^2
     relations placing r_p in the degree-<=4 extension k(q,x,y)
     over L_p, and r_q in the degree-<=2 extension over L_q.
  6. Slice shape: F_0 = c*a_0 + G_0 with G_0 free of a_0.

Out of scope (explicitly NOT asserted): the valuation bound
v_p(H_j) >= 2j, any transcendence claim for r_p/r_q over L_p/L_q,
the q-lemma, W-degree induction, global generation, Hilbert
series. No parity/slice-power/transposed-naming argument is used.

Run:
    python3 scripts/cas/check_plemma.py  # log: data/plemma.log
Prints PASS/FAIL per check plus a final `check_plemma OK` (exit 0/1).
"""

from sympy import Matrix, Poly, Rational, expand, symbols


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def main():
    ok = True
    x, y, z, p, q, a0 = symbols("x y z p q a0")

    # Verbatim dictionary (Tasks 4/6).
    J1 = 2 * p * z - y**2
    J2 = 2 * q * y - x**2
    G0 = (-p * q**3 * x * y * z + Rational(1, 3) * p * q**2 * x**3 * z
          + Rational(1, 3) * q**2 * x**3 * y**2 - Rational(1, 5) * q * x**5 * y
          + Rational(1, 35) * x**7)
    c = p**2 * q**4
    F0 = c * a0 + G0

    # 1. Specialization rows.
    J1p = expand(J1.subs(p, 0))
    J2p = expand(J2.subs(p, 0))
    J1q = expand(J1.subs(q, 0))
    J2q = expand(J2.subs(q, 0))
    ok &= _check("J1-mod-p", J1p - (-y**2) == 0)
    ok &= _check("J2-mod-p", J2p - (2 * q * y - x**2) == 0)
    ok &= _check("J1-mod-q", J1q - (2 * p * z - y**2) == 0)
    ok &= _check("J2-mod-q", J2q - (-x**2) == 0)

    # 2. Initial-form numerators.
    rp_num = (Rational(1, 3) * q**2 * x**3 * y**2
              - Rational(1, 5) * q * x**5 * y + Rational(1, 35) * x**7)
    rq_num = x**7 / 35
    G0p = expand(G0.subs(p, 0))
    G0q = expand(G0.subs(q, 0))
    ok &= _check("G0-mod-p-is-rp-num", expand(G0p - rp_num) == 0)
    ok &= _check("G0-mod-p-nonzero", G0p != 0)
    ok &= _check("G0-mod-q-is-rq-num", expand(G0q - rq_num) == 0)
    ok &= _check("G0-mod-q-nonzero", G0q != 0)
    # Exact pole orders: G0 has nonzero p-free and q-free parts.
    ok &= _check("vp-G0-zero", Poly(G0, p).nth(0) != 0)
    ok &= _check("vq-G0-zero", Poly(G0, q).nth(0) != 0)

    # 3. Denominator exponents e_p = 2, e_q = 4.
    ok &= _check("c-is-p2q4", expand(c - p**2 * q**4) == 0)
    ok &= _check("ord-p-c-2", Poly(c, p).degree() == 2)
    ok &= _check("ord-q-c-4", Poly(c, q).degree() == 4)

    # 4. Residue-field setup independence.
    det_p = expand(Matrix([q, y**2, 2 * q * y - x**2, z])
                   .jacobian([q, x, y, z]).det())
    ok &= _check("Lp-setup-minor-4xy", det_p - 4 * x * y == 0)
    ok &= _check("Lp-setup-minor-nonzero", det_p != 0)
    det_q = expand(Matrix([p, 2 * p * z - y**2, x**2])
                   .jacobian([p, x, y]).det())
    ok &= _check("Lq-setup-minor-4xy", det_q - 4 * x * y == 0)
    ok &= _check("Lq-setup-minor-nonzero", det_q != 0)

    # 5. Algebraicity witnesses (obstacle remark).
    ok &= _check("y2-in-Lp-gens", expand(-J1p - y**2) == 0)
    ok &= _check("x2-in-Lp-y", expand((2 * q * y - J2p) - x**2) == 0)
    ok &= _check("x2-in-Lq-gens", expand(-J2q - x**2) == 0)
    ok &= _check("rp-nonzero", expand(rp_num) != 0)
    ok &= _check("rq-nonzero", expand(rq_num) != 0)

    # 6. Slice shape F_0 = c*a_0 + G_0, G_0 free of a_0.
    audited = (p**2 * q**4 * a0 - p * q**3 * x * y * z
               + Rational(1, 3) * p * q**2 * x**3 * z
               + Rational(1, 3) * q**2 * x**3 * y**2
               - Rational(1, 5) * q * x**5 * y + Rational(1, 35) * x**7)
    ok &= _check("F0-is-c-a0-plus-G0", expand(F0 - audited) == 0)
    ok &= _check("G0-free-of-a0", Poly(G0, a0).degree() == 0)

    print("check_plemma OK" if ok else "check_plemma FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
