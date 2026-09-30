"""Plinth intersection sweep: compute im(D|_{A_w}) intersect K_w exactly over QQ.
Tests the plinth-module conjecture pl(D5) =?= pq*K + f13*K
(Conjecture conj:plinth-module): the expected dimension is
dim K_{w-2} + dim K_{w-13}. A weight with larger dimension, i.e. a
plinth direction outside (pq, f13), is flagged *** OUTSIDE (pq,f13) ***
and is a falsifier. q-primitive basis elements within the expected
dimension are the f13-family (info only).

K = k[p,q,J1,J2] is polynomial; (pq) is monomial => pq-divisibility
checked per K-monomial.
"""
from fractions import Fraction
from plinth_probe import (monomials_of_weight, apply_D_to_monomial, WT,
                          add_exp, tpoly)

J1_TERMS = [((0, 1, 0, 0, 1, 0), Fraction(2)), ((0, 0, 2, 0, 0, 0), Fraction(-1))]
J2_TERMS = [((0, 0, 1, 0, 0, 1), Fraction(2)), ((0, 0, 0, 2, 0, 0), Fraction(-1))]


def expand_K_monomial(a, b, c, d):
    """p^a q^b J1^c J2^d as dict A-exp -> coeff."""
    res = {(0, 0, 0, 0, 0, 0): Fraction(1)}
    for _ in range(a):
        res = {add_exp(m, (0, 0, 0, 0, 1, 0)): v for m, v in res.items()}
    for _ in range(b):
        res = {add_exp(m, (0, 0, 0, 0, 0, 1)): v for m, v in res.items()}
    for _ in range(c):
        nres = {}
        for m, v in res.items():
            for t, tc in J1_TERMS:
                k = add_exp(m, t)
                nres[k] = nres.get(k, Fraction(0)) + v * tc
        res = nres
    for _ in range(d):
        nres = {}
        for m, v in res.items():
            for t, tc in J2_TERMS:
                k = add_exp(m, t)
                nres[k] = nres.get(k, Fraction(0)) + v * tc
        res = nres
    return {k: v for k, v in res.items() if v != 0}


def K_basis_of_weight(w):
    out = []
    for c in range(w // 6 + 1):
        for d in range((w - 6 * c) // 4 + 1):
            r = w - 6 * c - 4 * d
            for a in range(r + 1):
                b = r - a
                out.append((a, b, c, d))
    return out


def nullspace(rows, ncols):
    """Nullspace of matrix given as list of dict rows. Returns list of vecs (dicts)."""
    M = [dict(r) for r in rows]
    nrows = len(M)
    pivots = {}  # col -> row
    prow = 0
    for col in range(ncols):
        piv = None
        for r in range(prow, nrows):
            if M[r].get(col, Fraction(0)) != 0:
                piv = r
                break
        if piv is None:
            continue
        M[prow], M[piv] = M[piv], M[prow]
        inv = M[prow][col]
        for k in list(M[prow].keys()):
            M[prow][k] /= inv
        for r in range(nrows):
            if r != prow and M[r].get(col, Fraction(0)) != 0:
                f = M[r][col]
                for k, v in M[prow].items():
                    M[r][k] = M[r].get(k, Fraction(0)) - f * v
                    if M[r][k] == 0:
                        del M[r][k]
        pivots[col] = prow
        prow += 1
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for f in free:
        v = {f: Fraction(1)}
        for col, pr in pivots.items():
            c = M[pr].get(f, Fraction(0))
            if c != 0:
                v[col] = -c
        basis.append(v)
    return basis


def plinth_intersection(w):
    """Returns list of (alpha_vec, K-element dict) spanning im(D) cap K_w."""
    pre = monomials_of_weight(w)
    kbasis = K_basis_of_weight(w)
    kexp = [expand_K_monomial(*t) for t in kbasis]
    # image rows
    img = {}
    for j, e in enumerate(pre):
        for m, c in apply_D_to_monomial(e).items():
            img.setdefault(m, {})[j] = c
    # full A_w support
    support = list(pre)  # D preserves weight; image monomials subset of weight-w monomials
    # build joint system: unknowns alpha (nK) + gamma (nPre); eq per support monomial m:
    #   sum_i alpha_i kexp_i(m) - sum_j gamma_j D_j(m) = 0
    nK, nP = len(kbasis), len(pre)
    rows = []
    for m in support:
        row = {}
        for i, ke in enumerate(kexp):
            if m in ke:
                row[i] = ke[m]
        dj = img.get(m, {})
        for j, c in dj.items():
            row[nK + j] = row.get(nK + j, Fraction(0)) - c
        # drop zero row? keep; nullspace handles
        rows.append({k: v for k, v in row.items() if v != 0})
    ns = nullspace(rows, nK + nP)
    out = []
    for v in ns:
        alpha = {i: v[i] for i in range(nK) if i in v and v[i] != 0}
        if not alpha:
            continue
        # assemble K element
        elem = {}
        for i, c in alpha.items():
            for m, kv in kexp[i].items():
                elem[m] = elem.get(m, Fraction(0)) + c * kv
        elem = {k: v2 for k, v2 in elem.items() if v2 != 0}
        out.append((alpha, elem, kbasis))
    return out, kbasis


def in_pq_ideal(alpha, kbasis):
    """alpha: dict i->coeff; True iff sum is in (pq)K (monomial ideal check)."""
    for i, c in alpha.items():
        if c == 0:
            continue
        a, b, cc, d = kbasis[i]
        if a < 1 or b < 1:
            return False
    return True


if __name__ == "__main__":
    import sys
    wmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    bad = 0
    for w in range(0, wmax + 1):
        res, kbasis = plinth_intersection(w)
        dimK = len(kbasis)
        # expected dim under pl = pq*K + f13*K (direct sum, Lemma plinth-direct)
        exp = len(K_basis_of_weight(w - 2)) + (
            len(K_basis_of_weight(w - 13)) if w >= 13 else 0)
        flag = "OK" if len(res) == exp else "*** OUTSIDE (pq,f13) ***"
        if len(res) != exp:
            bad += 1
        nq = sum(1 for (a, e, kb) in res if not in_pq_ideal(a, kb))
        print(f"w={w:3d} dimK={dimK:3d} dim(cap)={len(res):3d} "
              f"expected={exp:3d} qprim-directions={nq:3d} {flag}")
    if bad:
        print(f"plinth-cap FAILED: {bad} weights outside (pq,f13)")
        sys.exit(1)
    print("plinth-cap OK")
