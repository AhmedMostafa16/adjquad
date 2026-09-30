"""N=5-analog O1 attack script: a1a2*M in D5(B5) => c | M, degree by degree.

Claim (shift-equivalent to O1, paper/10-n6.tex eq:n6-Ckernel): every
M in K = k[p,q,J1,J2] with a1a2*M in D5(B5) is divisible by c = p^2*q^4
in K. Here B5 = k[a1..a5], D5(a1) = a2a3, D5(a2) = a3a4,
D5(a3) = a4a5, D5(a4) = D5(a5) = 0 (total-degree +1 homogeneous),
p = a4, q = a5, J1 = 2a1a4-a2^2, J2 = 2a2a5-a3^2.

Per total degree m: M over the degree-m piece of K (free-gen monomials
p^i*q^j*J1^k*J2^l, i+j+2k+2l = m), N over B5-monomials of degree m+1;
Sol_m = {(M,N) : a1a2*M + D5(N) = 0}. goods(m) = dim Sol_m -
dim ker(D5|B5_{m+1}); check goods(m) == free4(m-6), with EXPLICIT exact
witnesses N = G0*mu (F0 = c*a0 + G0, D5(F0) = 0, checked by expansion).
goods(m) > free4(m-6) would refute the analog (hence O1 itself).

Nullities mod-PRIME (1000003); witnesses exact over QQ. Evidence only.

Run:
    python3 scripts/cas/check_N5_O1.py  # log: data/n5_O1.log
Prints PASS/FAIL per check plus a final `check_N5_O1 OK` (exit 0/1).
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402

PRIME = 1000003
M_MAX = 12

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


# ---------------------------------------------------------------------------
# Exponent-tuple machinery on B5 = k[a1..a5] (positions 0..4).
# ---------------------------------------------------------------------------

def B_tuples(d):
    """All exponent 5-tuples of total degree d."""
    out = []

    def rec(idx, left, cur):
        if idx == 5:
            if left == 0:
                out.append(tuple(cur))
            return
        for e in range(left + 1):
            rec(idx + 1, left - e, cur + [e])

    rec(0, d, [])
    return out


def D5_tup(m):
    """D5 image of a B5-monomial tuple (dict tuple->int coeff)."""
    out = defaultdict(int)
    # a1->a2a3, a2->a3a4, a3->a4a5.
    for i, (t1, t2) in enumerate(((1, 2), (2, 3), (3, 4))):
        if m[i]:
            t = list(m)
            t[i] -= 1
            t[t1] += 1
            t[t2] += 1
            out[tuple(t)] += m[i]
    return {k: v for k, v in out.items() if v}


def _nullity(rows, cols):
    """Nullity of the matrix given by cols (each a {row: coeff} dict)."""
    n, p = len(rows), len(cols)
    ridx = {m: i for i, m in enumerate(rows)}
    M = [defaultdict(int) for _ in range(n)]
    for j, col in enumerate(cols):
        for nm, k in col.items():
            r = ridx.get(nm)
            if r is not None:
                M[r][j] = (M[r].get(j, 0) + k) % PRIME
    rank = 0
    for ccol in range(p):
        pv = None
        for r in range(rank, n):
            if M[r].get(ccol, 0) != 0:
                pv = r
                break
        if pv is None:
            continue
        M[rank], M[pv] = M[pv], M[rank]
        inv = pow(M[rank][ccol], PRIME - 2, PRIME)
        for cc in list(M[rank]):
            M[rank][cc] = (inv * M[rank][cc]) % PRIME
        for r in range(n):
            if r == rank:
                continue
            f = M[r].get(ccol, 0)
            if f == 0:
                continue
            for cc, vv in list(M[rank].items()):
                M[r][cc] = (M[r].get(cc, 0) - f * vv) % PRIME
                if M[r][cc] == 0:
                    del M[r][cc]
        M[rank].pop(ccol, None)
        rank += 1
    return p - rank


_ker_memo = {}


def kerdim_B(d):
    """dim ker(D5 : B5_d -> B5_{d+1}) over F_PRIME."""
    if d in _ker_memo:
        return _ker_memo[d]
    rows = B_tuples(d + 1)
    cols = [D5_tup(m) for m in B_tuples(d)]
    res = _nullity(rows, cols)
    _ker_memo[d] = res
    return res


def free4_tuples(d):
    """Free-gen exponent (i,j,k,l) with i+j+2k+2l = d (d >= 0)."""
    if d < 0:
        return []
    out = []
    for k in range(d // 2 + 1):
        for l in range((d - 2 * k) // 2 + 1):
            r = d - 2 * k - 2 * l
            for i in range(r + 1):
                out.append((i, r - i, k, l))
    return out


def free4(d):
    return len(free4_tuples(d))


# ---------------------------------------------------------------------------
# M-basis as SymPy B5-polys (exact, small) for the matrix columns.
# ---------------------------------------------------------------------------

_SYM = {}


def _sym():
    if not _SYM:
        from sympy import symbols
        a = symbols("a_0:6")
        a1, a2, a3, a4, a5 = a[1], a[2], a[3], a[4], a[5]
        _SYM.update(a=a, a1=a1, a2=a2, a3=a3, a4=a4, a5=a5,
                    p=a4, q=a5,
                    J1=2 * a1 * a4 - a2**2, J2=2 * a2 * a5 - a3**2)
    return _SYM


def M_basis_poly(m):
    """[(free-exp, B5-tuple-dict)] for p^i*q^j*J1^k*J2^l of degree m."""
    from sympy import Poly, expand
    s = _sym()
    out = []
    for (i, j, k, l) in free4_tuples(m):
        b = expand(s["p"]**i * s["q"]**j * s["J1"]**k * s["J2"]**l)
        d = {}
        for exp, c in Poly(b, s["a1"], s["a2"], s["a3"],
                           s["a4"], s["a5"]).as_dict().items():
            d[tuple(exp)] = int(c) % PRIME
        out.append(((i, j, k, l), d))
    return out


def _shift_a1a2(col):
    """Multiply a tuple-dict by a1*a2 (positions 0 and 1)."""
    out = {}
    for e, c in col.items():
        t = list(e)
        t[0] += 1
        t[1] += 1
        out[tuple(t)] = c
    return out


_nulltot_memo = {}


def nulldim_total(m):
    """Nullity of (M,N) |-> a1a2*M + D5(N); M deg m in K, N deg m+1."""
    if m in _nulltot_memo:
        return _nulltot_memo[m]
    rows = B_tuples(m + 2)
    cols = [_shift_a1a2(d) for (_, d) in M_basis_poly(m)]
    cols += [D5_tup(n) for n in B_tuples(m + 1)]
    res = _nullity(rows, cols)
    _nulltot_memo[m] = res
    return res


def goods_dim(m):
    """dim of the projection of Sol_m onto M-coords (rank-nullity)."""
    return nulldim_total(m) - kerdim_B(m + 1)


# ---------------------------------------------------------------------------
# Exact QQ witnesses: each c*mu is a solution (N = G0*mu).
# ---------------------------------------------------------------------------

def _F0_data():
    from sympy import Rational, expand
    s = _sym()
    a = s["a"]
    a0, a1, a2, a3, a4, a5 = (a[0], s["a1"], s["a2"], s["a3"],
                              s["a4"], s["a5"])
    c = a4**2 * a5**4
    F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
          + Rational(1, 3) * a4 * a5**2 * a3**3 * a1
          + Rational(1, 3) * a5**2 * a3**3 * a2**2
          - Rational(1, 5) * a5 * a3**5 * a2 + Rational(1, 35) * a3**7)
    G0 = expand(F0 - c * a0)
    return a, F0, c, G0


def _mu_poly(free_exp):
    s = _sym()
    i, j, k, l = free_exp
    return s["p"]**i * s["q"]**j * s["J1"]**k * s["J2"]**l


def main():
    from sympy import expand
    ok = True
    N = 5
    a, F0, c, G0 = _F0_data()
    s = _sym()
    # 1. M-basis lies in K; F0 available for the ladder.
    for name, g in [("p", s["p"]), ("q", s["q"]), ("J_1", s["J1"]),
                    ("J_2", s["J2"]), ("F_0", F0)]:
        ok &= check("D(%s)=0" % name, verify_D(g, a, N) is True)
    ok &= check("G0 is a0-free", a[0] not in G0.free_symbols)
    # 2. Seed ladder identity a1a2*c + D5(G0) = 0 (exact, from D5(F0) = 0).
    seed = expand(s["a1"] * s["a2"] * c + apply_D(G0, a, N))
    ok &= check("seed a1a2*c+D5(G0)=0", seed == 0)
    # 3. Per-degree divisibility.
    log.append("m  nulltot  kerB(m+1)  goods  free4(m-6)  verdict")
    for m in range(M_MAX + 1):
        nt = nulldim_total(m)
        kc = kerdim_B(m + 1)
        gd = nt - kc
        fc = free4(m - 6)
        wit_ok = True
        for fe in free4_tuples(m - 6):
            mu = _mu_poly(fe)
            w = expand(s["a1"] * s["a2"] * c * mu + apply_D(G0 * mu, a, N))
            if w != 0:
                wit_ok = False
                break
        if gd > fc:
            log.append("  %-3d %-7d %-10d %-5d %-11d ANALOG-REFUTED(+%d)"
                       % (m, nt, kc, gd, fc, gd - fc))
            ok &= check("m=%d no excess" % m, False)
        else:
            match = (gd == fc)
            log.append("  %-3d %-7d %-10d %-5d %-11d %s"
                       % (m, nt, kc, gd, fc,
                          "DIVISIBLE" if (match and wit_ok) else "MISMATCH"))
            ok &= check("m=%d goods==free4(m-6)=%d" % (m, fc), match)
            ok &= check("m=%d all c*mu witnessed (exact)" % m, wit_ok)
    for ln in log:
        print(ln)
    print("check_N5_O1 OK" if ok else "check_N5_O1 FAILED")
    try:
        os.makedirs("logs", exist_ok=True)
        with open("data/n5_O1.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N5_O1 OK" if ok
                       else "check_N5_O1 FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
