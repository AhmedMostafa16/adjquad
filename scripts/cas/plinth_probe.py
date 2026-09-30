"""Plinth probe: for target f in K_w, decide f in D(A_w) by linear algebra over QQ.
A = k[a0..a5], weights (8,5,3,2,1,1), D(a_n) = a_{n+1} a_{n+2} (a6=a7=0).
D preserves Fibonacci weight. For each weight w: basis of A_w monomials,
matrix of D, solve D(g) = f.
"""
import itertools
from fractions import Fraction

WT = (8, 5, 3, 2, 1, 1)
# D(a_n) as dict {monomial_exp_tuple: coeff}
DGEN = {
    0: {(0, 1, 1, 0, 0, 0): Fraction(1)},   # a1*a2
    1: {(0, 0, 1, 1, 0, 0): Fraction(1)},   # a2*a3
    2: {(0, 0, 0, 1, 1, 0): Fraction(1)},   # a3*a4
    3: {(0, 0, 0, 0, 1, 1): Fraction(1)},   # a4*a5
    4: {},
    5: {},
}


def add_exp(e1, e2):
    return tuple(a + b for a, b in zip(e1, e2))


def sub_exp(e1, n):
    l = list(e1)
    l[n] -= 1
    return tuple(l)


def monomials_of_weight(w):
    """All exponent tuples with sum e_i*WT_i == w (bounded search)."""
    maxes = [w // t + 1 for t in WT]
    out = []
    for e0 in range(maxes[0]):
        r0 = w - e0 * WT[0]
        if r0 < 0:
            break
        for e1 in range(maxes[1]):
            r1 = r0 - e1 * WT[1]
            if r1 < 0:
                break
            for e2 in range(maxes[2]):
                r2 = r1 - e2 * WT[2]
                if r2 < 0:
                    break
                for e3 in range(maxes[3]):
                    r3 = r2 - e3 * WT[3]
                    if r3 < 0:
                        break
                    # e4, e5 both weight 1
                    for e4 in range(r3 + 1):
                        e5 = r3 - e4
                        out.append((e0, e1, e2, e3, e4, e5))
    return out


def apply_D_to_monomial(e):
    """D(a^e) = sum_n e_n * a^{e - u_n} * D(a_n). Returns dict exp->coeff."""
    res = {}
    for n in range(6):
        if e[n] == 0:
            continue
        base = sub_exp(e, n)
        for dexp, c in DGEN[n].items():
            m = add_exp(base, dexp)
            res[m] = res.get(m, Fraction(0)) + e[n] * c
    return {k: v for k, v in res.items() if v != 0}


def rref_solve(rows, rhs, ncols):
    """Solve M x = rhs over QQ. rows: list of dict {col: val}.
    Returns one solution dict or None."""
    import copy
    M = [dict(r) for r in rows]
    b = list(rhs)
    nrows = len(M)
    pivots = []
    prow = 0
    prow_of_col = {}
    for col in range(ncols):
        piv = None
        for r in range(prow, nrows):
            if M[r].get(col, Fraction(0)) != 0:
                piv = r
                break
        if piv is None:
            continue
        M[prow], M[piv] = M[piv], M[prow]
        b[prow], b[piv] = b[piv], b[prow]
        inv = M[prow][col]
        # normalize pivot row
        for k in list(M[prow].keys()):
            M[prow][k] /= inv
        b[prow] /= inv
        for r in range(nrows):
            if r != prow and M[r].get(col, Fraction(0)) != 0:
                f = M[r][col]
                for k, v in M[prow].items():
                    M[r][k] = M[r].get(k, Fraction(0)) - f * v
                    if M[r][k] == 0:
                        del M[r][k]
                b[r] -= f * b[prow]
        prow_of_col[col] = prow
        pivots.append(col)
        prow += 1
    # check consistency
    for r in range(prow, nrows):
        if not M[r] and b[r] != 0:
            return None
    for r in range(prow):
        if not M[r] and b[r] != 0:
            return None
    sol = {}
    for col, pr in prow_of_col.items():
        sol[col] = b[pr]
    return sol


def in_image(target, w):
    """target: dict exp->coeff (weight w). Returns (bool, solution)."""
    basis = monomials_of_weight(w)
    idx = {m: i for i, m in enumerate(basis)}
    rows = []  # one row per basis monomial of image? Build M: cols=preimage basis
    # M[img_idx][pre_idx] — build as list of dict rows over preimage cols
    img_index = {}
    row_list = []

    def get_row(m):
        if m not in img_index:
            img_index[m] = len(row_list)
            row_list.append({})
        return row_list[img_index[m]]

    for j, e in enumerate(basis):
        d = apply_D_to_monomial(e)
        for m, c in d.items():
            assert sum(a * t for a, t in zip(m, WT)) == w, (m, w)
            get_row(m)[j] = c
    rhs = [Fraction(0)] * len(row_list)
    for m, c in target.items():
        if m not in img_index:
            return False, None  # target has monomial outside image support rows... actually need row
        rhs[img_index[m]] = c
    sol = rref_solve(row_list, rhs, len(basis))
    return (sol is not None), sol


def poly_from_str_vars():
    # helper namespace: exponents for named monomials
    E = {}
    E['p'] = (0, 0, 0, 0, 1, 0)
    E['q'] = (0, 0, 0, 0, 0, 1)
    E['pq'] = (0, 0, 0, 0, 1, 1)
    E['p2'] = (0, 0, 0, 0, 2, 0)
    E['q2'] = (0, 0, 0, 0, 0, 2)
    E['c'] = (0, 0, 0, 0, 2, 4)
    E['x'] = (0, 0, 0, 1, 0, 0)
    E['y'] = (0, 0, 1, 0, 0, 0)
    E['z'] = (0, 1, 0, 0, 0, 0)
    return E


def tpoly(*terms):
    d = {}
    for coeff, e in terms:
        d[e] = d.get(e, Fraction(0)) + Fraction(coeff)
    return {k: v for k, v in d.items() if v != 0}


def weight_of(target):
    for m in target:
        return sum(a * t for a, t in zip(m, WT))
    return 0


if __name__ == "__main__":
    E = poly_from_str_vars()
    J1 = tpoly((2, add_exp((0, 1, 0, 0, 0, 0), (0, 0, 0, 0, 1, 0))),
               (-1, (0, 0, 2, 0, 0, 0)))
    J2 = tpoly((2, add_exp((0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 0, 1))),
               (-1, (0, 0, 0, 2, 0, 0)))
    probes = {
        "1": tpoly((1, (0, 0, 0, 0, 0, 0))),
        "p": tpoly((1, E['p'])),
        "q": tpoly((1, E['q'])),
        "pq": tpoly((1, E['pq'])),
        "p^2": tpoly((1, E['p2'])),
        "q^2": tpoly((1, E['q2'])),
        "J1": J1,
        "J2": J2,
        "c=p^2q^4": tpoly((1, E['c'])),
    }
    for name, t in probes.items():
        w = weight_of(t)
        ok, sol = in_image(t, w)
        nmon = len(monomials_of_weight(w))
        print(f"w={w:3d} nmons={nmon:5d} {name:10s} in-D(A): {ok}")
