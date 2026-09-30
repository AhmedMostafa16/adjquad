"""Transported witness: D6(phi(F46)) = 0 by direct expansion.

phi : k[a0..a5] -> k[a1..a6], a_i |-> a_{i+1}, is the graded shift
isomorphism of thm:recursion (verified in scripts/cas/check_N6_shift.py).
Hence D6(phi(F46)) = phi(D5(F46)) = 0 follows from the intertwining
identity -- but this script checks it INDEPENDENTLY by direct expansion
of the 79 shifted witness terms (simultaneous .xreplace, cf. the SymPy
subs pitfall noted in check_N6_shift.py), not by invoking intertwining.

Expects data/witness_w46.txt (79 integral terms, thm:F46).

Run:
    python3 scripts/cas/check_N6_transport_F.py  # log: data/n6/transport_F.log
Prints PASS/FAIL per check plus a final `transport-F OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import verify_D  # noqa: E402

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def load_terms(path):
    from sympy import Rational
    terms = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            head, coeff = line.split()
            terms.append((Rational(coeff), tuple(map(int, head.split(",")))))
    return terms


def main():
    from sympy import Poly, expand, symbols
    ok = True
    a = symbols("a_0:7")
    terms = load_terms("data/witness_w46.txt")
    ok &= check("F46 loads 79 terms (got %d)" % len(terms), len(terms) == 79)
    F = sum(co * a[0] ** e[0] * a[1] ** e[1] * a[2] ** e[2]
            * a[3] ** e[3] * a[4] ** e[4] * a[5] ** e[5] for co, e in terms)
    ok &= check("D5(F46)=0 (sanity, N=5 side)", verify_D(F, a[:6], 5) is True)
    Phi = expand(F.xreplace({a[j]: a[j + 1] for j in range(6)}))
    ok &= check("phi(F46) has no a0", a[0] not in Phi.free_symbols)
    ok &= check("D6(phi(F46))=0 identically (direct expansion)",
               verify_D(Phi, a, 6) is True)
    P = Poly(Phi, a[1])
    ok &= check("phi(F46) has a1-degree 4", P.degree() == 4)
    top = expand(P.nth(4))
    ok &= check("transported top 121550625*a5^6*a6^8 (=(18375/4) normalized)",
               expand(top - 121550625 * a[5]**6 * a[6]**8) == 0)
    v5 = min(e[0] for e in Poly(top, a[5]).as_dict())
    v6 = min(e[0] for e in Poly(top, a[6]).as_dict())
    log.append("  v5(top)=%d (transported J4 needs >=8: OUTSIDE)  v6(top)=%d"
               % (v5, v6))
    ok &= check("transported top outside (a5^8*a6^8): v5=6<8",
               v5 == 6 and v6 == 8)
    FIB6 = (13, 8, 5, 3, 2, 1, 1)
    ws = {sum(e[i] * FIB6[i] for i in range(7))
          for e in Poly(Phi, *a).as_dict()}
    log.append("  weights=%s" % sorted(ws))
    ok &= check("phi(F46) uniform Fibonacci weight 46", ws == {46})
    for ln in log:
        print(ln)
    print("transport-F OK" if ok else "transport-F FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/transport_F.log", "w") as fh:
            fh.write("\n".join(
                log + ["transport-F OK" if ok else "transport-F FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
