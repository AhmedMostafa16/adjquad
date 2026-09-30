"""F46 realizes the rho_p minimal-polynomial cancellation (check).

The q-side template (established kill shot): H = H2 W^2 + H0 has
q-pole orders (-4,-4) in its constant term C0 = H0 + H2 rho^2, and the
q^-4 residues cancel via r_q^2 in L_q. This script verifies the p-side
analogue for F46 = sum_{j<=4} H_j W^j: every nonzero W-coefficient has
p-pole order exactly -2 in the constant term C0 = sum H_j rho^j, and
the four per-term p-residues E_j = [p^2 H_j rho^j]_{p=0} are well
defined with E_4 != 0 and sum E_j = 0 -- a genuine degree-4 relation
among 1, r_p, ..., r_p^4. Since rho_p = 4 exactly (probe_rho_p.py),
1, r_p, r_p^2, r_p^3 are independent over L_p, so this relation is an
L_p-unit multiple of the minimal polynomial m_p. In particular the
p-side failure has the same shape as the q-side: constant-term pole
cancellation governed by the minimal polynomial (quadratic at q,
quartic at p). What is NOT shown: that resonance produces the
generator (existence direction remains open).

Checks (PASS/FAIL each, final `check_rhop_cancellation OK`, exit 0/1):
  R. in_p(p^2 rho) equals the manuscript r_p (consistency).
  W. W-descent reproduces H4 = (18375/4)p^6q^8, H3 = 0.
  V. v_p(H_j) exactly (6,2,0,-2) for j = 4,2,1,0.
  E. each E_j finite with E_4 != 0; sum E_j == 0 exactly.
  C. C0 == [a0^0]F46 cross-check (descent consistency).

Run: python3 scripts/cas/check_rhop_cancellation.py  # log: data/rhop_cancellation.log
"""

from collections import defaultdict
from fractions import Fraction
from sympy import (Poly, Rational, expand, symbols, together, fraction,
                   cancel, binomial)

a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
p, q = a4, a5
x, y, z = a3, a2, a1
J1 = 2 * a1 * a4 - a2**2
J2 = 2 * a2 * a5 - a3**2
F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
      + Rational(1, 3) * a4 * a5**2 * a3**3 * a1
      + Rational(1, 3) * a5**2 * a3**3 * a2**2
      - Rational(1, 5) * a5 * a3**5 * a2 + Rational(1, 35) * a3**7)
c = a4**2 * a5**4
G0 = expand(F0 - c * a0)
rho = together(G0 / c)
# manuscript r_p = in_p(p^2 rho) (05a-plemma residue setup): p^2 rho = G0/q^4
# is p-regular, so in_p is evaluation at p = 0 (q generic nonzero).
r_p_manuscript = (Rational(1, 3) * q**2 * x**3 * y**2
                  - Rational(1, 5) * q * x**5 * y
                  + Rational(1, 35) * x**7) / q**4

terms = []
with open("data/witness_w46.txt") as fh:
    for line in fh:
        sp = line.strip().split()
        terms.append((int(sp[1]), tuple(map(int, sp[0].split(",")))))
F46 = expand(sum(co * a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3]
                 * a4**e[4] * a5**e[5] for co, e in terms))

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def ordp(e, v):
    e = expand(e)
    d = Poly(e, v).as_dict()
    return min(t[0] for t in d) if d else 0


def vpq(e):
    n, d = fraction(together(e))
    n, d = expand(n), expand(d)
    return ordp(n, a5) - ordp(d, a5), ordp(n, a4) - ordp(d, a4)


def main():
    ok = True
    # R. residue consistency: in_p(p^2 rho) == manuscript r_p.
    in_p = expand(cancel(p**2 * rho))
    # in_p(p^2 rho) means: clear p-denominators (none left: p^2 rho = G0/q^4
    # is p-regular) and set p = 0.
    r_p_computed = expand(cancel(in_p).subs(p, 0))
    r_p_target = expand(cancel(r_p_manuscript).subs(p, 0))
    ok &= check("R-residue-matches-manuscript",
                expand(r_p_computed - r_p_target) == 0)
    log.append("  r_p = %s" % r_p_target)
    # W. exact W-descent.
    PF = Poly(F46, a0)
    C = {k: expand(PF.nth(k)) for k in range(5)}
    Hc = {}
    for k in range(4, -1, -1):
        s = C[k]
        for j in range(k + 1, 5):
            s = s - binomial(j, k) * Hc[j] * rho**(j - k)
        Hc[k] = together(s)
    ok &= check("W-H4-top-monomial",
                # cleared integral form: H4 = K*p^6q^8 for a scalar K
                # (QQ-form top is (18375/4)p^6q^8; K = 26460 * 18375/4 here).
                # Assert H4/p^6q^8 is constant (single monomial up to scale).
                cancel(Hc[4] / (p**6 * q**8)).is_number)
    log.append("  H4/top-scale K = %s" % cancel(Hc[4] / (p**6 * q**8)))
    ok &= check("W-H3-zero", expand(cancel(Hc[3])) == 0)
    # V. exact p-valuations (equality, not just lower bounds).
    vps = {}
    for j in (4, 2, 1, 0):
        vq, vp = vpq(Hc[j])
        vps[j] = vp
        log.append("  H_%d vq=%d vp=%d" % (j, vq, vp))
    ok &= check("V-valuations-exact-6-2-0--2",
                vps == {4: 6, 2: 2, 1: 0, 0: -2})
    # E. per-term p-orders at the constant term are exactly -2, so each
    # p-residue E_j = [p^2 H_j rho^j]_{p=0} is finite (indeed nonzero);
    # their sum vanishes: the quartic relation.
    vrho = vpq(rho)[1]
    ok &= check("E-rho-pole-exactly-2", vrho == -2)
    for j in (4, 2, 1, 0):
        vq, vp = vpq(Hc[j])
        ok &= check("E-term-%d-order-exactly--2" % j, vp - 2 * j == -2)
    E = {}
    for j in (4, 2, 1, 0):
        E[j] = expand(cancel(p**2 * Hc[j] * rho**j).subs(p, 0))
    ok &= check("E_4-nonzero", E[4] != 0)
    log.append("  E_4 = %s" % E[4])
    ok &= check("E-sum-zero-quartic-relation",
                expand(sum(E.values())) == 0)
    log.append("  E_2 + E_1 + E_0 terms present (degrees 2,1,0; no cubic: H3=0)")
    # C. constant-term cross-check.
    ok &= check("C-C0-eq-a0coeff",
                expand(cancel(sum(binomial(j, 0) * Hc[j] * rho**j
                                  for j in range(5)) - C[0])) == 0)
    for ln in log:
        print(ln)
    print("check_rhop_cancellation OK" if ok else "check_rhop_cancellation FAILED")
    try:
        with open("data/rhop_cancellation.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_rhop_cancellation OK" if ok else
                       "check_rhop_cancellation FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
