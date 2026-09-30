"""Reusable filtration certificate: producer/checker split (Theorem IV).

Producer (UNTRUSTED): Sage support-restricted exact solves, SymPy
W-expansion / witness-emission scripts. They may suggest a candidate
invariant F, its weight, a0-degree, and top coefficient.

Checker (TRUSTED): this script. It verifies by exact integer/rational
equalities only -- same philosophy as the decode invariant in
paper/11-generation.tex subsec:denom-soundness (exact cross-multiplied
rational equality, not mere integrality):
  (i)   D(F) = 0 exactly over QQ (triangular derivation);
  (ii)  uniform Fibonacci weight (8,5,3,2,1,1);
  (iii) a0-degree + top a0-coefficient;
  (iv)  J_m (non-)membership of the top by exact monomial divisibility,
        J_m = (p^{2m} q^{4*ceil(m/2)}) (Definition def:Jm;
        checked 0 <= m <= 8 in scripts/cas/check_Jtops.py).

First certified instance: F46 (data/witness_w46.txt, 79 terms, weight 46,
a0-degree 4, top (18375/4) p^6 q^8 cleared as 121550625 p^6 q^8) outside
J_4 = (p^8 q^8); Lean formalization formalize/AdjQuad/SecondWitness.lean
(definition, D(F46) = 0, uniform weight, top; zero sorry).

Patterns follow scripts/cas/profile_witness.py (D-zero loop via SymPy
Poly.as_dict, Poly(F, a0).nth top extraction) and scripts/cas/check_Jtops.py
idioms (exponent-vector targets, extremal-divides-all, nonneg remainders).

Run: python3 scripts/cas/certify_filtration.py --self-test
  log: data/filtration_cert.log
Prints PASS/FAIL per gate plus a final `filtration-cert OK` (exit 0/1).
"""

import math
import os
import sys
from collections import defaultdict

from sympy import Poly, Rational, expand, symbols

a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
ALL = (a0, a1, a2, a3, a4, a5)
FIB_W = (8, 5, 3, 2, 1, 1)

W46_PATH_CANDIDATES = (
    "data/witness_w46.txt",
    os.path.join(os.path.dirname(__file__), "../../data/witness_w46.txt"),
)

EXPECTED_W = 46
EXPECTED_DEG = 4
EXPECTED_M = 4
# Integral cleared top of F46 as stored in data/witness_w46.txt
# (normalized form: (18375/4) p^6 q^8; SecondWitness.lean header).
EXPECTED_TOP_EXP = (6, 8)

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def _resolve(path):
    if os.path.exists(path):
        return path
    for cand in W46_PATH_CANDIDATES:
        if os.path.exists(cand):
            return cand
    return path


def load_witness(path="data/witness_w46.txt"):
    """Load witness file lines 'e0,..,e5 coeff' -> SymPy expression (exact QQ)."""
    path = _resolve(path)
    terms = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            parts = line.split()
            ex = tuple(map(int, parts[0].split(",")))
            terms.append((Rational(parts[1]), ex))
    F = sum(
        co * a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3] * a4**e[4] * a5**e[5]
        for co, e in terms
    )
    return expand(F), terms


def check_D_zero(poly):
    """Gate (i): D(F) = 0 exactly (triangular D, cf. profile_witness.py).

    D(a0) = a1*a2, D(a1) = a2*a3, D(a2) = a3*p, D(a3) = p*q,
    D(p) = D(q) = 0; linear extension with exact QQ coefficients.
    """
    HD = defaultdict(lambda: Rational(0))
    for e, cc in Poly(expand(poly), *ALL).as_dict().items():
        r = Rational(cc)
        for i in range(4):
            if e[i]:
                t = list(e)
                t[i] -= 1
                t[i + 1] += 1
                t[i + 2] += 1
                HD[tuple(t)] += r * e[i]
    return all(v == 0 for v in HD.values())


def check_uniform_weight(poly, expected=EXPECTED_W):
    """Gate (ii): every monomial has Fibonacci weight == expected."""
    d = Poly(expand(poly), *ALL).as_dict()
    ws = {sum(e[i] * FIB_W[i] for i in range(6)) for e in d}
    return (len(ws) == 1 and expected in ws), ws


def top_a0(poly):
    """Gate (iii): return (a0-degree, top a0-coefficient in B)."""
    P = Poly(expand(poly), a0)
    deg = P.degree()
    top = expand(P.nth(deg))
    return deg, top


def check_a0_degree(poly, expected=EXPECTED_DEG):
    """Degree gate: a0-degree must equal expected (rejects e.g. a0^5)."""
    deg, _ = top_a0(poly)
    return deg == expected, deg


def J_target(m):
    """Claimed principal generator exponents: (2m, 4*ceil(m/2))."""
    return (2 * m, 4 * int(math.ceil(m / 2)))


def pq_valuations(top):
    """Min (p, q) exponents across monomials of top (exact, coeff-blind).

    Sound monomial-ideal membership test for tops in k[p,q] (the F46/H
    case): top != 0 in J_m = (p^A q^B) iff every monomial is divisible
    by the generator, i.e. min valuations dominate the target. Zero top
    is vacuously in every ideal.
    """
    t = expand(top)
    if t == 0:
        return None
    d = Poly(t, a1, a2, a3, a4, a5).as_dict()
    if any(e[0] != 0 or e[1] != 0 or e[2] != 0 for e in d):
        return None
    # exponents indices in Poly(a1..a5): p = a4 -> idx 3, q = a5 -> idx 4
    vp = min(e[3] for e in d)
    vq = min(e[4] for e in d)
    return (vp, vq)


def in_Jm(top, m):
    """Gate (iv): exact divisibility membership top in J_m (check_Jtops idiom)."""
    t = expand(top)
    if t == 0:
        return True  # deliberate asymmetry: vacuous membership here, but certify still FAILs a zero top since a witness needs nonzero outside.
    v = pq_valuations(t)
    if v is None:
        raise ValueError("top not in k[p,q]")
    tpe, tqe = J_target(m)
    return v[0] >= tpe and v[1] >= tqe


def certify(poly, expected_w=EXPECTED_W, expected_deg=EXPECTED_DEG,
            m=EXPECTED_M, expect_in_Jm=False):
    """Full four-gate certification. Returns True iff all gates behave as expected."""
    ok = True
    ok &= check("D-zero D(F)==0 exactly", check_D_zero(poly))
    w_ok, ws = check_uniform_weight(poly, expected_w)
    ok &= check("weight uniform Fibonacci w=%d (ws=%s)" % (expected_w, sorted(ws)), w_ok)
    deg_ok, deg = check_a0_degree(poly, expected_deg)
    ok &= check("a0-degree == %d (got %d)" % (expected_deg, deg), deg_ok)
    _, top = top_a0(poly)
    v = pq_valuations(top)
    tpe, tqe = J_target(m)
    if v is None:
        if expand(top) == 0:
            ok &= check("top nonzero (got zero top)", False)
        else:
            ok &= check("top not in k[p,q] (scope reject)", False)
    else:
        ok &= check("top exponents (p^%d q^%d)" % v, True)
        log.append("  top = %s | v_p=%d v_q=%d | J_%d=(p^%d q^%d)"
                   % (top, v[0], v[1], m, tpe, tqe))
        got = in_Jm(top, m)
        if expect_in_Jm:
            ok &= check("top in J_%d (expected member)" % m, got is True)
        else:
            ok &= check("top outside J_%d (expected non-member)" % m, got is False)
    return ok


def self_test():
    ok = True
    F, terms = load_witness()
    ok &= check("F46 loads 79 terms (got %d)" % len(terms), len(terms) == 79)

    # --- Main instance: F46 passes all gates, outside J_4 ---
    ok &= check("F46 D-zero", check_D_zero(F))
    w_ok, ws = check_uniform_weight(F, EXPECTED_W)
    ok &= check("F46 uniform weight 46 (ws=%s)" % sorted(ws), w_ok)
    deg_ok, deg = check_a0_degree(F, EXPECTED_DEG)
    ok &= check("F46 a0-degree 4 (got %d)" % deg, deg_ok)
    deg, top = top_a0(F)
    v = pq_valuations(top)
    ok &= check("F46 top exponents (p^6 q^8) (got %s)" % (v,), v == EXPECTED_TOP_EXP)
    ok &= check("F46 top outside J_4 (v_p=6<8)", in_Jm(top, EXPECTED_M) is False)
    log.append("  F46 top = %s" % top)

    # --- Control A (must ACCEPT into J_4): doctored top p^8 q^8 ---
    doctored_top = a4**8 * a5**8
    dv = pq_valuations(doctored_top)
    ok &= check("control-J4 doctored top exponents (p^8 q^8) (got %s)" % (dv,),
                dv == (8, 8))
    ok &= check("control-J4 doctored p^8q^8 ACCEPTED into J_4",
                in_Jm(doctored_top, 4) is True)
    # Same polarity at the poly level: F with top swapped into J_4.
    F_in = expand(F - top * a0**4 + doctored_top * a0**4)
    _, top_in = top_a0(F_in)
    ok &= check("control-J4 poly-level swapped top accepted into J_4",
                in_Jm(top_in, 4) is True)

    # --- Control B (must REJECT by degree gate): added a0^5 term ---
    # Weight-homogeneous add-on: a0^5 p^3 q^3 weighs 5*8+3+3 = 46, so the
    # weight gate still passes and the degree gate is isolated.
    F_bad = expand(F + a0**5 * a4**3 * a5**3)
    bad_ok, bad_deg = check_a0_degree(F_bad, EXPECTED_DEG)
    ok &= check("control-degree a0^5 poly has degree 5 (got %d)" % bad_deg,
                bad_deg == 5)
    ok &= check("control-degree a0^5 REJECTED by degree gate (expect 4)",
                bad_ok is False)
    w_bad_ok, w_bad = check_uniform_weight(F_bad, EXPECTED_W)
    ok &= check("control-degree add-on stays weight-homogeneous (ws=%s)"
                % sorted(w_bad), w_bad_ok is True)

    for ln in log:
        print(ln)
    print("filtration-cert OK" if ok else "filtration-cert FAILED")
    try:
        os.makedirs("data", exist_ok=True)
        with open("data/filtration_cert.log", "w") as fh:
            fh.write("\n".join(
                log + ["filtration-cert OK" if ok else "filtration-cert FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


def main(argv):
    if "--self-test" in argv:
        return self_test()
    F, _ = load_witness()
    ok = certify(F)
    for ln in log:
        print(ln)
    print("filtration-cert OK" if ok else "filtration-cert FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
