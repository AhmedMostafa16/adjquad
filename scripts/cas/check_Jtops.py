"""J_m top ideals as pure C5-side algebra (Theorem IIa, all m).

Tops: top(F0) = c = p^2 q^4, top(H) = h_2 = 11025 p^4 q^4 (Theorem
thm:F0-invariant, Counterexample header; 11025 a unit in
characteristic zero). For m >= 0, J_m is the K-span of the tops
c^e h_2^r with e + 2r = m. Since c^e h_2^r = 11025^r p^{2e+4r}
q^{4e+4r}, every generator has p-exponent 2m; the extremal generator
(r = floor(m/2), e = m mod 2) attains the minimal q-exponent
4*ceil(m/2) and divides all others up to a unit power of 11025.
Hence J_m = (p^{2m} q^{4*ceil(m/2)}) principal for all m
(Definition def:Jm; consumed verbatim by Tasks 3-5).

Pure integer arithmetic on (p, q) exponent vectors; stdlib only.

Run: python3 scripts/cas/check_Jtops.py  # log: data/Jtops.log
Prints PASS/FAIL per m plus a final `check_Jtops OK` (exit 0/1).
"""

import math
import os

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


# Exponent vectors in (p, q): c = p^2 q^4, h_2 = p^4 q^4 (unit 11025^r tracked separately).
C_EXP = (2, 4)
H_EXP = (4, 4)

M_MAX = 8


def generators(m):
    """List of (e, r, pe, qe, unit_pow) with e + 2r = m."""
    out = []
    for r in range(m // 2 + 1):
        e = m - 2 * r
        pe = C_EXP[0] * e + H_EXP[0] * r
        qe = C_EXP[1] * e + H_EXP[1] * r
        out.append((e, r, pe, qe, r))
    return out


def target(m):
    """Claimed principal generator exponents: (2m, 4*ceil(m/2))."""
    return (2 * m, 4 * int(math.ceil(m / 2)))


# Theorem IIc inputs (Task 4): F46 top coefficient (18375/4) p^6 q^8
# (Theorem thm:F46), F0 top c = p^2 q^4 (Theorem thm:F0-invariant).
F46_TOP_EXP = (6, 8)


def main():
    ok = True
    for m in range(M_MAX + 1):
        gens = generators(m)
        tpe, tqe = target(m)
        r_star, e_star = m // 2, m % 2
        # Extremal generator present with exactly the target exponents.
        ext = [(e, r, pe, qe, u) for (e, r, pe, qe, u) in gens
               if r == r_star and e == e_star]
        ok &= check("m=%d extremal (e=%d,r=%d) present" % (m, e_star, r_star),
                    len(ext) == 1)
        if ext:
            ok &= check("m=%d extremal exponents = target (%d,%d)" % (m, tpe, tqe),
                        (ext[0][2], ext[0][3]) == (tpe, tqe))
        # p-exponent uniformity: 2e+4r = 2m for every generator.
        ok &= check("m=%d all pe == 2m = %d" % (m, 2 * m),
                    all(pe == 2 * m for (_, _, pe, _, _) in gens))
        # Extremal divides every generator: nonneg (p, q) remainders,
        # unit quotient a power of 11025.
        div = all(pe >= tpe and qe >= tqe for (_, _, pe, qe, _) in gens)
        ok &= check("m=%d extremal divides all others" % m, div)
        for (e, r, pe, qe, u) in gens:
            ok &= check("m=%d gen(e=%d,r=%d) quo (dp=%d,dq=%d,du=11025^%d) nonneg"
                        % (m, e, r, pe - tpe, qe - tqe, r_star - u),
                        pe - tpe >= 0 and qe - tqe >= 0 and r_star - u >= 0
                        and (pe - tpe, qe - tqe) == (0, 4 * (r_star - r)))
        # Closed forms from the brief: even case generator list, odd case factor-one-c.
        if m % 2 == 0:
            k = m // 2
            ok &= check("m=%d=2k even generators 11025^r p^4k q^(8k-4r)" % m,
                        all(pe == 4 * k and qe == 8 * k - 4 * r and u == r
                            for (e, r, pe, qe, u) in gens))
        else:
            k = m // 2
            prev = {(e, r) for (e, r, _, _, _) in generators(2 * k)}
            ok &= check("m=%d=2k+1 J_odd = c * J_even" % m,
                        all(e >= 1 and (e - 1, r) in prev
                            for (e, r, _, _, _) in gens))
        log.append("  m=%d J=(p^%d q^%d) gens=%s"
                   % (m, tpe, tqe,
                      [(pe, qe, u) for (_, _, pe, qe, u) in gens]))
    # Birth windows: min C5-side weight at a0-degree m is min over
    # e+2r=m of 14e+24r (K-multiplier mu=1); monomial a0^m weighs 8m.
    # A primitive degree-m direction born below the C5 window is new;
    # table verified by exhaustive enumeration over (e, r).
    minc5_expect = {0: 0, 1: 14, 2: 24, 3: 38, 4: 48, 5: 62, 6: 72,
                    7: 86, 8: 96}
    for m, want in sorted(minc5_expect.items()):
        vals = [14 * e + 24 * r for r in range(m // 2 + 1)
                for e in [m - 2 * r]]
        got = min(vals)
        ok &= check("minC5(%d) = %d" % (m, want), got == want)
        ok &= check("gap(%d) = [%d,%d] nonempty" % (m, 8 * m, want - 1),
                    8 * m <= want - 1 or m == 0)
        log.append("  minC5(%d)=%d gap=[%d,%d]" % (m, got, 8 * m, want - 1))
    # Theorem IIc (Task 4): top(F46.F0) = c * top(F46), exact integer
    # arithmetic on exponent vectors. Tops multiply over the domain
    # B[a_0]; coefficient (18375/4) != 0 in characteristic zero.
    f_pe = F46_TOP_EXP[0] + C_EXP[0]
    f_qe = F46_TOP_EXP[1] + C_EXP[1]
    j5_pe, j5_qe = target(5)
    ok &= check("F-F0-outside-J5 top exponents (p^%d q^%d)" % (f_pe, f_qe),
                (f_pe, f_qe) == (8, 12))
    ok &= check("F-F0-outside-J5 J5 target (p^%d q^%d)" % (j5_pe, j5_qe),
                (j5_pe, j5_qe) == (10, 12))
    ok &= check("F-F0-outside-J5 v_p = 8 < 10 = 2*5", f_pe == 8 < 2 * 5 == j5_pe)
    ok &= check("F-F0-outside-J5 p-deficit (dp=%d) blocks J5 membership"
                % (f_pe - j5_pe),
                f_pe - j5_pe < 0 and f_qe - j5_qe >= 0)
    ok &= check("F-F0-outside-J5 top (18375/4)p^8q^12 outside J5", f_pe < j5_pe)
    log.append("  F-F0-outside-J5 top=(18375/4)p^%d q^%d J5=(p^%d q^%d) "
               "weight=60 a0deg=5" % (f_pe, f_qe, j5_pe, j5_qe))
    # Tower seeds: top(F46.H) = top(F46) + h_2 and top(F46.F0^2) =
    # top(F46) + 2c, exact integer arithmetic on exponent vectors.
    # Tops multiply over the domain B[a_0]; coefficients nonzero in
    # characteristic zero.
    h_pe = F46_TOP_EXP[0] + H_EXP[0]
    h_qe = F46_TOP_EXP[1] + H_EXP[1]
    j6_pe, j6_qe = target(6)
    ok &= check("F-H-outside-J6 top exponents (p^%d q^%d)" % (h_pe, h_qe),
                (h_pe, h_qe) == (10, 12))
    ok &= check("F-H-outside-J6 J6 target (p^%d q^%d)" % (j6_pe, j6_qe),
                (j6_pe, j6_qe) == (12, 12))
    ok &= check("F-H-outside-J6 v_p = 10 < 12 = 2*6", h_pe == 10 < 2 * 6 == j6_pe)
    ok &= check("F-H-outside-J6 p-deficit (dp=%d) blocks J6 membership"
                % (h_pe - j6_pe),
                h_pe - j6_pe < 0 and h_qe - j6_qe >= 0)
    ok &= check("F-H-outside-J6 top outside J6", h_pe < j6_pe)
    log.append("  F-H-outside-J6 top=(18375/4).11025p^%d q^%d J6=(p^%d q^%d) "
               "weight=70 a0deg=6" % (h_pe, h_qe, j6_pe, j6_qe))
    f2_pe = F46_TOP_EXP[0] + 2 * C_EXP[0]
    f2_qe = F46_TOP_EXP[1] + 2 * C_EXP[1]
    ok &= check("F-F02-outside-J6 top exponents (p^%d q^%d)" % (f2_pe, f2_qe),
                (f2_pe, f2_qe) == (10, 16))
    ok &= check("F-F02-outside-J6 v_p = 10 < 12 = 2*6", f2_pe == 10 < 2 * 6 == j6_pe)
    ok &= check("F-F02-outside-J6 p-deficit (dp=%d) blocks J6 membership"
                % (f2_pe - j6_pe),
                f2_pe - j6_pe < 0 and f2_qe - j6_qe >= 0)
    ok &= check("F-F02-outside-J6 top outside J6", f2_pe < j6_pe)
    log.append("  F-F02-outside-J6 top=(18375/4)p^%d q^%d J6=(p^%d q^%d) "
               "weight=74 a0deg=6" % (f2_pe, f2_qe, j6_pe, j6_qe))
    for ln in log:
        print(ln)
    print("check_Jtops OK" if ok else "check_Jtops FAILED")
    try:
        os.makedirs("data", exist_ok=True)
        with open("data/Jtops.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_Jtops OK" if ok else "check_Jtops FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
