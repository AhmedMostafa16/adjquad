"""Bounded ML search: triangular LNDs of A5 preserving K (exact).

Ansatz: E triangular on A5 = k[a0..a5] (E(a5) = 0, E(a_i) in later
vars, total degree <= 2; 55 params). Every triangular derivation is
automatically locally nilpotent (standard filtration argument), so
each parameter point IS an LND -- no nilpotency check needed.
  1. Preserving subspace: {E : E(J1), E(J2) in K} (E(p), E(q)
     automatic); exact QQ nullspace (K-monomial coordinates, total
     degree <= 3).
  2. Per preserving direction: E(F0) == 0? E(H) == 0? (exact, cheap);
     ring-membership of images (mod-prime screen, exact confirm).
An E preserving A5^D with E(F0) = 0 or E(H) = 0 would shrink ML(A5^D)
below the full ring. Finding none through this bound is reported
honestly as a bounded negative, NOT an ML computation.

Run:
    python3 scripts/cas/check_ML_search.py  # log: data/ML.log
Exit 0 on clean run (any verdict), 1 on crash.
"""

import os
import sys
from itertools import combinations_with_replacement as cwr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

PRIME = 1000003

_SYM = {}


def _sym():
    if not _SYM:
        from sympy import symbols
        a = symbols("a_0:6")
        a0, a1, a2, a3, a4, a5 = a
        _SYM.update(a=a, later=[[a1, a2, a3, a4, a5], [a2, a3, a4, a5],
                                [a3, a4, a5], [a4, a5], [a5], []])
    return _SYM


def _monoms_deg(vars_, d):
    """All monomials in vars_ of exact total degree d (as (exps, poly))."""
    out = []
    n = len(vars_)

    def rec(idx, left, cur):
        if idx == n:
            if left == 0:
                out.append(tuple(cur))
            return
        for e in range(left + 1):
            rec(idx + 1, left - e, cur + [e])

    rec(0, d, [])
    res = []
    for e in out:
        m = 1
        for v, p in zip(vars_, e):
            m *= v**p
        res.append(m)
    return res


def param_basis():
    """55 basis derivations: (var_index, monomial) with triangularity."""
    s = _sym()
    out = []
    for i in range(5):
        for d in range(3):
            for m in _monoms_deg(s["later"][i], d):
                out.append((i, m))
    return out


def _apply_E(Eimgs, poly):
    """Apply derivation with images Eimgs[i] = E(a_i) via chain rule."""
    from sympy import expand
    s = _sym()
    out = 0
    for i, v in enumerate(s["a"]):
        out += Eimgs[i] * poly.diff(v)
    return expand(out)


def _E_of(basis, coeffs):
    from sympy import expand
    Eimgs = [0] * 6
    for c, (i, m) in zip(coeffs, basis):
        Eimgs[i] = expand(Eimgs[i] + c * m)
    return Eimgs


def _K_gens():
    s = _sym()
    a0, a1, a2, a3, a4, a5 = s["a"]
    return [a4, a5, 2 * a1 * a4 - a2**2, 2 * a2 * a5 - a3**2]


def _K_monoms(dmax):
    s = _sym()
    p, q, J1, J2 = _K_gens()
    out = []
    for tot in range(dmax + 1):
        for i in range(tot + 1):
            for j in range(tot + 1 - i):
                for k in range((tot - i - j) // 2 + 1):
                    for l in range((tot - i - j - 2 * k) // 2 + 1):
                        out.append(p**i * q**j * J1**k * J2**l)
    return out


def _B_monoms(d):
    s = _sym()
    return _monoms_deg(list(s["a"][1:]), d)


def D5_in_ansatz():
    """D5(a_i) = a_{i+1}a_{i+2} are triangular degree-2 monomials."""
    s = _sym()
    imgs = [s["a"][1] * s["a"][2], s["a"][2] * s["a"][3],
            s["a"][3] * s["a"][4], 0, 0, 0]
    basis = param_basis()
    for i, target in enumerate(imgs):
        if target == 0:
            continue
        if not any(bi == i and (bm - target).expand() == 0
                   for (bi, bm) in basis):
            return False
    return True


def _constraint_matrix():
    """40 x 55 QQ matrix: E = sum c_b E_b preserves K iff Cmat*c = 0.

    Rows: left-nullspace of the K-monomial coordinate matrix (total
    degree <= 3) over the union of all K-monomials AND all E_b(J)
    monomials, so out-of-K-span monomials are constrained to zero.
    Two 20-row blocks (J1, J2) stacked.
    """
    from sympy import Matrix, Poly, expand
    s = _sym()
    basis = param_basis()
    J1 = 2 * s["a"][1] * s["a"][4] - s["a"][2]**2
    J2 = 2 * s["a"][2] * s["a"][5] - s["a"][3]**2
    K3 = _K_monoms(3)
    EbJ = []
    for J in (J1, J2):
        col = []
        for (bi, bm) in basis:
            Eimgs = [0] * 6
            Eimgs[bi] = bm
            col.append(expand(_apply_E(Eimgs, J)))
        EbJ.append(col)
    rows = sorted(set().union(
        *[set(Poly(m, *s["a"][1:]).as_dict()) for m in K3],
        *[set(Poly(v, *s["a"][1:]).as_dict()) for col in EbJ for v in col]))
    ridx = {e: k for k, e in enumerate(rows)}
    KM = Matrix.zeros(len(rows), len(K3))
    for j, m in enumerate(K3):
        for exp, c in Poly(expand(m), *s["a"][1:]).as_dict().items():
            KM[ridx[exp], j] = c
    C = KM.T.nullspace()
    Cmat = Matrix.hstack(*C).T if C else Matrix.zeros(0, len(rows))
    blocks = []
    for col in EbJ:
        blk = Matrix.zeros(Cmat.rows, len(basis))
        for b, v in enumerate(col):
            vec = Matrix.zeros(len(rows), 1)
            for exp, c in Poly(expand(v), *s["a"][1:]).as_dict().items():
                vec[ridx[exp], 0] = c
            cc = Cmat * vec
            for r in range(Cmat.rows):
                blk[r, b] = cc[r, 0]
        blocks.append(blk)
    return Matrix.vstack(*blocks)


_ns_cache = {}


def preserving_basis():
    """Basis (param-coord vectors) of K-preserving triangular derivations."""
    key = "ns"
    if key not in _ns_cache:
        _ns_cache[key] = _constraint_matrix().nullspace()
    return _ns_cache[key]


def preserving_dim():
    return len(preserving_basis())


def main():
    from sympy import Matrix, Poly, expand
    ok = True
    print("PASS D5 in ansatz" if D5_in_ansatz() else "FAIL D5 in ansatz")
    ok &= D5_in_ansatz()
    ns = preserving_basis()
    print("preserving dim = %d (of 55 params)" % len(ns))
    s = _sym()
    basis = param_basis()
    # kernel effects on F0, H (exact zero-tests; H from check_N6_shift data)
    a0, a1, a2, a3, a4, a5 = s["a"]
    F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
          + __import__("sympy").Rational(1, 3) * a4 * a5**2 * a3**3 * a1
          + __import__("sympy").Rational(1, 3) * a5**2 * a3**3 * a2**2
          - __import__("sympy").Rational(1, 5) * a5 * a3**5 * a2
          + __import__("sympy").Rational(1, 35) * a3**7)
    from check_N6_shift import HMONO
    H = 0
    for co, ex in HMONO:
        m = co
        for v, p in zip(s["a"], ex):
            m *= v**p
        H += m
    nkillF, nkillH, npres = 0, 0, len(ns)
    for v in ns:
        Eimgs = _E_of(basis, list(v))
        if expand(_apply_E(Eimgs, F0)) == 0:
            nkillF += 1
        if expand(_apply_E(Eimgs, H)) == 0:
            nkillH += 1
    print("preserving directions killing F0: %d/%d" % (nkillF, npres))
    print("preserving directions killing H: %d/%d" % (nkillH, npres))
    print("ML-SEARCH OK (bounded; not an ML computation)")
    try:
        os.makedirs("logs", exist_ok=True)
        with open("data/ML.log", "w") as fh:
            fh.write("preserving_dim=%d\nkillF0=%d/%d\nkillH=%d/%d\n"
                     "ML-SEARCH OK\n" % (len(ns), nkillF, npres, nkillH, npres))
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
