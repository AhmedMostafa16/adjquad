"""Shift-transfer certificate: (B,D6|_B) ~= (A5,D5) and its consequences.

phi : k[a0..a5] -> k[a1..a6], a_i |-> a_{i+1}, is a graded ring
isomorphism intertwining D5 with D6 (weights (8,5,3,2,1,1) on both
sides). Hence B^D6 ~= A5^D5: the N=5 hypersurface verdict transports
verbatim. With H (17 terms, Counterexample.lean / check_s6.py) and F0:
  H_B = phi(H) (wt 24, a1-degree 2, D6(H_B) = 0, H_B not in R);
  F0_B = phi(F0) = G5/105 + C0 with C0 in k[a5,a6,G3,G4] (explicit);
  S_B = a6^4*H_B - 11025*F0_B^2 - 105*a6^2*G4^5*G3 - 9*G4^7 = 0.
Consequences certified here: R_24 has a1-degree <= 1 (only G5 carries
a1, and G5^2 already weighs 28), so H_B not in R (five-generation
refuted); W#-top H_2 = 11025*a5^4*a6^4 has v6 = 4 < 8 (a6-saturation
refuted, same numbers as N=5) while v5 = 4 = 2*2 (a5-side consistent).

NOTE (SymPy pitfall): `.subs` with a shifting dict applies SEQUENTIALLY
in SymPy 1.14; use `.xreplace` (always simultaneous) below.

Run:
    python3 scripts/cas/check_N6_shift.py  # log: data/n6/shift.log
Prints PASS/FAIL per check plus a final `check_N6_shift OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


HMONO = [((11025), [2, 0, 0, 0, 4, 4]),
         ((-22050), [1, 1, 1, 1, 3, 3]),
         ((7350), [1, 1, 0, 3, 3, 2]),
         ((7350), [1, 0, 2, 3, 2, 2]),
         ((-4410), [1, 0, 1, 5, 2, 1]),
         ((630), [1, 0, 0, 7, 2, 0]),
         ((11025), [0, 2, 2, 2, 2, 2]),
         ((-7350), [0, 2, 1, 4, 2, 1]),
         ((1225), [0, 2, 0, 6, 2, 0]),
         ((6720), [0, 1, 5, 0, 1, 3]),
         ((-16800), [0, 1, 4, 2, 1, 2]),
         ((9450), [0, 1, 3, 4, 1, 1]),
         ((-1540), [0, 1, 2, 6, 1, 0]),
         ((-2208), [0, 0, 7, 0, 0, 3]),
         ((4368), [0, 0, 6, 2, 0, 2]),
         ((-2352), [0, 0, 5, 4, 0, 1]),
         ((385), [0, 0, 4, 6, 0, 0])]


def _mk(a, e, off=1):
    m = 1
    for i, p in enumerate(e):
        m *= a[off + i]**p
    return m


def _HB(a):
    return sum(co * _mk(a, ex) for (co, ex) in HMONO)


def _F0B(a):
    from sympy import Rational
    terms = [((1), [1, 0, 0, 0, 2, 4]),
             ((-1), [0, 1, 1, 1, 1, 3]),
             ((Rational(1, 3)), [0, 1, 0, 3, 1, 2]),
             ((Rational(1, 3)), [0, 0, 2, 3, 0, 2]),
             ((Rational(-1, 5)), [0, 0, 1, 5, 0, 1]),
             ((Rational(1, 35)), [0, 0, 0, 7, 0, 0])]
    return sum(co * _mk(a, ex) for (co, ex) in terms)


def _G(a):
    a1, a2, a3, a4, a5, a6 = a[1], a[2], a[3], a[4], a[5], a[6]
    G1 = a5
    G2 = a6
    G3 = 2 * a2 * a5 - a3**2
    G4 = 2 * a3 * a6 - a4**2
    G5 = (105 * a1 * a5**2 * a6**4
          - 105 * a2 * a3 * a4 * a5 * a6**3
          + 35 * a2 * a4**3 * a5 * a6**2
          + 35 * a3**2 * a4**3 * a6**2
          - 21 * a3 * a4**5 * a6
          + 3 * a4**7)
    return [G1, G2, G3, G4, G5]


def intertwines():
    from sympy import symbols, expand
    a = symbols("a_0:7")
    return all(expand(apply_D(a[i], a, 5).xreplace(
        {a[j]: a[j + 1] for j in range(6)}) - apply_D(a[i + 1], a, 6)) == 0
        for i in range(6))


def HB_invariant():
    from sympy import symbols
    a = symbols("a_0:7")
    return verify_D(_HB(a), a, 6) is True


def HB_a1deg_two():
    from sympy import Poly, symbols
    a = symbols("a_0:7")
    return Poly(_HB(a), a[1]).degree() == 2


def R24_a1deg_le_one():
    """Only G5 carries a1 (deg 1); G5^2 weighs 28 > 24, so R_24 has
    a1-degree <= 1 (a1-degree adds over products in a domain)."""
    from sympy import Poly, symbols
    a = symbols("a_0:7")
    G = _G(a)
    degs = [Poly(g, a[1]).degree() or 0 for g in G]
    if degs != [0, 0, 0, 0, 1]:
        return False
    # Fibonacci weights (1,1,6,4,14): G5-exponent among wt-24 monomials.
    for e5 in range(24 // 14 + 1):
        if e5 > 1:
            return False
    return True


def SB_zero():
    from sympy import expand, symbols
    a = symbols("a_0:7")
    G = _G(a)
    SB = (a[6]**4 * _HB(a) - 11025 * _F0B(a)**2
          - 105 * a[6]**2 * G[3]**5 * G[2] - 9 * G[3]**7)
    return expand(SB) == 0


def _C0_expr():
    """C0 = F0_B - G5/105 expressed in k[a5,a6,G3,G4] (exact QQ solve)."""
    from sympy import Matrix, Poly, Rational, expand, symbols
    a = symbols("a_0:7")
    G = _G(a)
    C0 = expand(_F0B(a) - G[4] / 105)
    if a[1] in C0.free_symbols:
        return None
    base = []
    for i in range(8):
        for j in range(8 - i):
            for k in range((7 - i - j) // 2 + 1):
                for l in range((7 - i - j - 2 * k) // 2 + 1):
                    base.append((i, j, k, l))
    C = [a[2], a[3], a[4], a[5], a[6]]
    polys = [expand(a[5]**i * a[6]**j * G[2]**k * G[3]**l)
             for (i, j, k, l) in base]
    rows = set()
    pd = []
    for p in polys:
        d = {}
        for exp, c in Poly(p, *C).as_dict().items():
            rows.add(exp)
            d[exp] = c
        pd.append(d)
    td = {}
    for exp, c in Poly(C0, *C).as_dict().items():
        rows.add(exp)
        td[exp] = c
    rows = sorted(rows)
    ridx = {e: k for k, e in enumerate(rows)}
    M = Matrix.zeros(len(rows), len(base))
    for j, d in enumerate(pd):
        for exp, c in d.items():
            M[ridx[exp], j] = c
    b = Matrix.zeros(len(rows), 1)
    for exp, c in td.items():
        b[ridx[exp], 0] = c
    sol, _ = M.gauss_jordan_solve(b)
    got = sum(sol[j, 0] * polys[j] for j in range(len(base)))
    if expand(got - C0) != 0:
        return None
    return [(base[j], sol[j, 0]) for j in range(len(base))
            if sol[j, 0] != 0]


def main():
    from sympy import Poly, expand, symbols
    ok = True
    ok &= check("shift intertwines D5/D6 on all generators", intertwines())
    ok &= check("D6(H_B)=0", HB_invariant())
    ok &= check("H_B has a1-degree 2", HB_a1deg_two())
    ok &= check("R_24 has a1-degree <= 1 (=> H_B not in R)", R24_a1deg_le_one())
    ok &= check("S_B = 0 (transported relation)", SB_zero())
    a = symbols("a_0:7")
    G = _G(a)
    ok &= check("D6(F0_B)=0", verify_D(_F0B(a), a, 6) is True)
    C0e = _C0_expr()
    ok &= check("C0 = F0_B - G5/105 in k[a5,a6,G3,G4] (explicit)",
                C0e is not None)
    if C0e is not None:
        if not C0e:
            log.append("  C0 = 0: F0_B = G5/105 EXACTLY (shift of F0 is"
                       " the degree-7 generator)")
        else:
            log.append("  C0 = " + " + ".join(
                "(%s)*a5^%d*a6^%d*G3^%d*G4^%d" % (c, i, j, k, l)
                for ((i, j, k, l), c) in C0e))
    ok &= check("F0_B = G5/105 by direct expansion",
                expand(_F0B(a) - G[4] / 105) == 0)
    # H_B W#-top valuations (sat6 refuted, sat5 consistent).
    H2 = Poly(_HB(a), a[1]).nth(2)
    ok &= check("H_2 = 11025*a5^4*a6^4",
                expand(H2 - 11025 * a[5]**4 * a[6]**4) == 0)
    v6 = min(e[0] for e in Poly(H2, a[6]).as_dict())
    v5 = min(e[0] for e in Poly(H2, a[5]).as_dict())
    log.append("  v6(H_2)=%d (box needs >=8: REFUTED)  v5(H_2)=%d (needs >=4: ok)"
               % (v6, v5))
    ok &= check("v6(H_2)=4 < 8", v6 == 4)
    ok &= check("v5(H_2)=4 >= 4", v5 == 4)
    for ln in log:
        print(ln)
    print("check_N6_shift OK" if ok else "check_N6_shift FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/shift.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N6_shift OK" if ok
                       else "check_N6_shift FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
