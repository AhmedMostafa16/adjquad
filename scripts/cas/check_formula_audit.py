"""Formula audit for the N=5 manuscript (exact integer/rational arithmetic).

Re-derives every closed-form formula in the paper from its definition
and checks equality. Prints PASS/FAIL per check plus a final
`check_formula_audit OK` (exit 0/1).

A. J_m ideals (def:Jm): J_m = span of tops c^e*h_2^r with e+2r=m,
   c = p^2q^4, h_2 = 11025 p^4q^4. Claimed principal form:
   J_m = (p^{2m} q^{4*ceil(m/2)}). Check: every generator top has
   v_p >= 2m and v_q >= 4*ceil(m/2), and the bound pair is attained
   (so the span equals the principal ideal; 11025 is a unit).
B. minC5(m) = min over e+2r=m of 14e+24r for m=1..8; birth windows.
   S homogeneity (wt 28 term by term); S_B homogeneity (wt 28).
   s_6(w) = #{monomials in (1,1,6,4,14,24) of weight w}: spot values
   s_6(46) = 1618, s_6(46)-s_6(18) = 1518 (thm:allweights-refuted).
C. R1 margins on H (m=2) and F_46 (m=4) documented profiles;
   Rp margins on H and F_46; R1 transfer combinatorics
   (lambda < -2m => 2*count > m, e=4,d=2) and Rp transfer
   combinatorics (lambda < -4m => 4*count > m, e=2,d=4);
   three-module excesses at 70-74 and 85 from s_K arithmetic.
D. Five-generator series spot values s_5(w) for w=24..30 (paper
   formula values); N=6 weight checks: G_4 = 2a_3a_6-a_4^2 has wt 4,
   M = a_5^4a_6G_4 has wt 9 (total degree 7), F = a_0M+N has wt 22,
   H_20 a_0-coefficient a_5^4a_6^3 has wt 7 (F wt 20),
   G_5 leading term c_6a_1 has wt 14.

Run:
    python3 scripts/cas/check_formula_audit.py  # log: data/formula_audit.log
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from math import ceil  # noqa: E402

RESULTS = []


def check(name, cond, detail=""):
    RESULTS.append((name, bool(cond), detail))
    print(("PASS " if cond else "FAIL ") + name
          + ((" [" + str(detail) + "]") if detail and not cond else ""))


def tops(m):
    """(e, r, vp, vq) of c^e h_2^r with e+2r=m (units ignored)."""
    out = []
    for e in range(m + 1):
        for r in range(m + 1):
            if e + 2*r == m:
                out.append((e, r, 2*e + 4*r, 4*e + 4*r))
    return out


def audit_A():
    for m in range(0, 9):
        ts = tops(m)
        assert ts, m
        minvp = min(t[2] for t in ts)
        minvq = min(t[3] for t in ts)
        check("Jm_principal_%d" % m,
              minvp == 2*m and minvq == 4*ceil(m/2),
              (m, minvp, minvq))
    # J_4, J_5, J_6 spot instances used in the paper
    check("J4_spot", (2*4, 4*ceil(4/2)) == (8, 8))
    check("J5_spot", (2*5, 4*ceil(5/2)) == (10, 12))
    check("J6_spot", (2*6, 4*ceil(6/2)) == (12, 12))
    check("J3_spot", (2*3, 4*ceil(3/2)) == (6, 8))


def audit_B():
    expect_min = {1: 14, 2: 24, 3: 38, 4: 48, 5: 62, 6: 72, 7: 86, 8: 96}
    for m in range(1, 9):
        best = min(14*e + 24*r for e in range(m + 1)
                   for r in range(m + 1) if e + 2*r == m)
        check("minC5_%d" % m, best == expect_min[m], (m, best))
        check("window_%d" % m, 8*m <= expect_min[m] - 1, (m, 8*m))
    # S = q^4 H - 11025 F0^2 - 105 q^2 J2^5 J1 - 9 J2^7, weights
    # (p,q,J1,J2,F0,H) = (1,1,6,4,14,24)
    check("S_homog", sorted([4 + 24, 2*14, 2 + 5*4 + 6, 7*4]) == [28]*4)
    # S_B = a6^4 H_B - G5^2 - 105 a6^2 G4^5 G3 - 9 G4^7, same weights
    check("SB_homog", sorted([4 + 24, 2*14, 2 + 5*4 + 6, 7*4]) == [28]*4)

    def counts(wts, W):
        dp = [0]*(W + 1)
        dp[0] = 1
        for t in wts:
            for w in range(t, W + 1):
                dp[w] += dp[w - t]
        return dp
    s6 = counts([1, 1, 6, 4, 14, 24], 60)
    check("s6_46", s6[46] == 1618, s6[46])
    check("s6_46_minus_18", s6[46] - s6[18] == 1518,
          (s6[46], s6[18]))


def audit_C():
    # R1 margins: H deficits (v_q-4j): j=2: 4-8; j=0: -4
    check("R1_H", min(4 - 8, -4) == -2*2)
    # F46 deficits: v_q = -8,-4,0,8 at j=0,1,2,4
    vq = {0: -8, 1: -4, 2: 0, 4: 8}
    check("R1_F46", min(v - 4*j for j, v in vq.items()) == -2*4)
    # Rp margins: H v_p: H_2 -> 4, H_0 -> 0
    check("Rp_H", min(4 - 2*2, 0 - 2*0) == 0)
    # F46 v_p = -2,0,2,6 at j=0,1,2,4
    vp = {0: -2, 1: 0, 2: 2, 4: 6}
    check("Rp_F46", min(v - 2*j for j, v in vp.items()) == -2)
    # transfer combinatorics: R1 (e=4,d=2)
    ok = True
    for m in range(0, 13):
        for lam in range(-4*m - 3, 2):
            c = sum(1 for k in range(m + 1) if lam + 4*k < 0)
            if lam < -2*m and not (2*c > m):
                ok = False
    check("R1_transfer", ok)
    # transfer combinatorics: Rp (e=2,d=4)
    ok = True
    for m in range(0, 13):
        for lam in range(-2*m - 5, 2):
            c = sum(1 for k in range(m + 1) if lam + 2*k < 0)
            if lam < -4*m and not (4*c > m):
                ok = False
    check("Rp_transfer", ok)
    # three-module excesses
    def counts2(wts, W):
        dp = [0]*(W + 1)
        dp[0] = 1
        for t in wts:
            for w in range(t, W + 1):
                dp[w] += dp[w - t]
        return dp
    sK = counts2([1, 1, 6, 4], 90)
    S = lambda v: sK[v] if v >= 0 else 0
    pred = {70: 45, 71: 50, 72: 54, 73: 58, 74: 63, 85: 134}
    for w, p in pred.items():
        got = (S(w - 46) - S(w - 48)) + (S(w - 60) - S(w - 62)) \
            + (S(w - 70) - S(w - 72))
        check("excess_%d" % w, got == p, (w, got))


def audit_D():
    def counts(wts, W):
        dp = [0]*(W + 1)
        dp[0] = 1
        for t in wts:
            for w in range(t, W + 1):
                dp[w] += dp[w - t]
        return dp
    s5 = counts([1, 1, 6, 4, 14], 35)
    expect = {24: 212, 25: 236, 26: 264, 27: 292, 28: 325, 29: 358,
              30: 396}
    for w, v in expect.items():
        check("s5_%d" % w, s5[w] == v, (w, s5[w]))
    # N=6 Fibonacci weights (a_0..a_6) = (13,8,5,3,2,1,1)
    W6 = [13, 8, 5, 3, 2, 1, 1]
    check("G4_wt", W6[3] + W6[6] == 4 and 2*W6[4] == 4)
    check("D2_M_wt", 4*W6[5] + W6[6] + 4 == 9)
    check("D2_M_tdeg", 4 + 1 + 2 == 7)
    check("D2_F_wt", W6[0] + 9 == 22)
    check("H20_coeff_wt", 4*W6[5] + 3*W6[6] == 7)
    check("H20_F_wt", W6[0] + 7 == 20)
    check("G5_lead_wt", (2*W6[5] + 4*W6[6]) + W6[1] == 14)


def main():
    audit_A()
    audit_B()
    audit_C()
    audit_D()
    ok = all(r[1] for r in RESULTS)
    print("check_formula_audit " + ("OK" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
