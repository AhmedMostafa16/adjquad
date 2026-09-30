"""O1-descent attack script: a2a3*M in D6(C) => c6 | M, degree by degree.

O1 (paper/10-n6.tex, Theorem thm:n6-descent) is the last gate for the N=6
B-level generation: every M in C^D6 with a2a3*M in D6(C) is divisible by
c6 = a5^2*a6^4 in C^D6 (whence a1-degree induction gives K6 ⊆ R).
Here C = k[a2..a6], C^D6 = k[a5,a6,G3,G4] (free; G3 = 2a2a5-a3^2,
G4 = 2a3a6-a4^2), D6(a2) = a3a4, D6(a3) = a4a5, D6(a4) = a5a6,
D6(a5) = D6(a6) = 0 (total-degree +1 homogeneous, so fixed-degree linear
algebra applies).

Per total degree m: M ranges over the degree-m piece of C^D6 (free-gen
monomials a5^i*a6^j*G3^k*G4^l, i+j+2k+2l = m), N over C-monomials of
degree m+1; solutions of a2a3*M + D6(N) = 0 form a linear space Sol_m.
With goods(m) = dim Sol_m - dim ker(D6|C_{m+1}) (rank-nullity on the
projection Sol_m -> M-coords) and free4(d) the degree-d count in the
free 4-gen ring:
  goods(m) == free4(m-6), and each c6*mu (mu a free-gen monomial of
  degree m-6) is exhibited as a solution with EXPLICIT exact N
  (N = N5*mu/105 from D6(G5) = 0, checked by expansion over QQ),
proves the projection equals c6*C^D6_{m-6}: every solution M IS
divisible by c6 in C^D6 (monomial divisor => term-wise check is exact).
goods(m) > free4(m-6) would be an O1 COUNTEREXAMPLE (reported as such).

Nullities are mod-PRIME (1000003), cross-checked at m <= 6 against the
exact-SymPy t1 stats of check_N6_kernel.py ((5,0),(8,0),(14,0),(20,0),
(30,0),(41,1)); explicit witnesses are exact over QQ. Evidence only:
O1 in full generality stays open.

Run:
    python3 scripts/cas/check_N6_O1.py  # log: data/n6/O1.log
Prints PASS/FAIL per check plus a final `check_N6_O1 OK` (exit 0/1).
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
# Exponent-tuple polytime machinery on C = k[a2..a6] (positions 0..4).
# ---------------------------------------------------------------------------

def C_tuples(d):
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


def D6C_tup(m):
    """D6 image of a C-monomial tuple (dict tuple->int coeff)."""
    out = defaultdict(int)
    # a2->a3a4, a3->a4a5, a4->a5a6.
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


_kerC_memo = {}


def kerdim_C(d):
    """dim ker(D6 : C_d -> C_{d+1}) over F_PRIME."""
    if d in _kerC_memo:
        return _kerC_memo[d]
    rows = C_tuples(d + 1)
    cols = [D6C_tup(m) for m in C_tuples(d)]
    res = _nullity(rows, cols)
    _kerC_memo[d] = res
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
# M-basis as SymPy C-polys (exact, small) for the matrix columns.
# ---------------------------------------------------------------------------

_SYM = {}


def _sym():
    if not _SYM:
        from sympy import symbols
        a = symbols("a_0:7")
        a2, a3, a4, a5, a6 = a[2], a[3], a[4], a[5], a[6]
        _SYM.update(a=a, a2=a2, a3=a3, a4=a4, a5=a5, a6=a6,
                    G3=2 * a2 * a5 - a3**2, G4=2 * a3 * a6 - a4**2)
    return _SYM


def M_basis_poly(m):
    """[(free-exp, C-tuple-dict)] for a5^i*a6^j*G3^k*G4^l of degree m."""
    from sympy import Poly, expand
    s = _sym()
    out = []
    for (i, j, k, l) in free4_tuples(m):
        b = expand(s["a5"]**i * s["a6"]**j * s["G3"]**k * s["G4"]**l)
        d = {}
        for exp, c in Poly(b, s["a2"], s["a3"], s["a4"],
                           s["a5"], s["a6"]).as_dict().items():
            d[tuple(exp)] = int(c) % PRIME
        out.append(((i, j, k, l), d))
    return out


def _shift_a2a3(col):
    """Multiply a tuple-dict by a2*a3 (positions 0 and 1)."""
    out = {}
    for e, c in col.items():
        t = list(e)
        t[0] += 1
        t[1] += 1
        out[tuple(t)] = c
    return out


_nulltot_memo = {}


def nulldim_total(m):
    """Nullity of (M,N) |-> a2a3*M + D6(N); M deg m in C^D6, N deg m+1."""
    if m in _nulltot_memo:
        return _nulltot_memo[m]
    rows = C_tuples(m + 2)
    cols = [_shift_a2a3(d) for (_, d) in M_basis_poly(m)]
    cols += [D6C_tup(n) for n in C_tuples(m + 1)]
    res = _nullity(rows, cols)
    _nulltot_memo[m] = res
    return res


def goods_dim(m):
    """dim of the projection of Sol_m onto M-coords (rank-nullity)."""
    return nulldim_total(m) - kerdim_C(m + 1)


# ---------------------------------------------------------------------------
# Exact QQ witnesses: each c6*mu is a solution (N = -N5*mu/105).
# ---------------------------------------------------------------------------

def _G5_data():
    from sympy import expand
    s = _sym()
    a = s["a"]
    a1, a5, a6 = a[1], a[5], a[6]
    G5 = (105 * a1 * a5**2 * a6**4
          - 105 * s["a2"] * s["a3"] * s["a4"] * a5 * a6**3
          + 35 * s["a2"] * s["a4"]**3 * a5 * a6**2
          + 35 * s["a3"]**2 * s["a4"]**3 * a6**2
          - 21 * s["a3"] * s["a4"]**5 * a6
          + 3 * s["a4"]**7)
    c6 = a5**2 * a6**4
    N5 = expand(G5 - 105 * a1 * c6)
    return a, G5, c6, N5


def _mu_poly(free_exp):
    s = _sym()
    i, j, k, l = free_exp
    return s["a5"]**i * s["a6"]**j * s["G3"]**k * s["G4"]**l


def main():
    from sympy import Rational, expand
    ok = True
    N = 6
    a, G5, c6, N5 = _G5_data()
    s = _sym()
    # 1. M-basis lies in C^D6; G5 available for the ladder.
    for name, g in [("a_5", s["a5"]), ("a_6", s["a6"]), ("G_3", s["G3"]),
                    ("G_4", s["G4"]), ("G_5", G5)]:
        ok &= check("D(%s)=0" % name, verify_D(g, a, N) is True)
    ok &= check("N5 is a1-free", a[1] not in N5.free_symbols)
    # 2. Seed ladder identity a2a3*c6 + D6(N5/105) = 0 (exact):
    #    D6(G5) = 105*c6*a2a3 + D6(N5) = 0 since D6(c6) = 0.
    seed = expand(a[2] * a[3] * c6 + apply_D(N5 / 105, a, N))
    ok &= check("seed a2a3*c6+D6(N5/105)=0", seed == 0)
    # 3. Per-degree divisibility.
    log.append("m  nulltot  kerC(m+1)  goods  free4(m-6)  verdict")
    for m in range(M_MAX + 1):
        nt = nulldim_total(m)
        kc = kerdim_C(m + 1)
        gd = nt - kc
        fc = free4(m - 6)
        wit_ok = True
        for fe in free4_tuples(m - 6):
            mu = _mu_poly(fe)
            w = expand(a[2] * a[3] * c6 * mu
                       + apply_D(N5 * mu / 105, a, N))
            if w != 0:
                wit_ok = False
                break
        if gd > fc:
            log.append("  %-3d %-7d %-10d %-5d %-11d O1-COUNTEREXAMPLE(+%d)"
                       % (m, nt, kc, gd, fc, gd - fc))
            ok &= check("m=%d no excess (O1 holds)" % m, False)
        else:
            match = (gd == fc)
            log.append("  %-3d %-7d %-10d %-5d %-11d %s"
                       % (m, nt, kc, gd, fc,
                          "DIVISIBLE" if (match and wit_ok) else "MISMATCH"))
            ok &= check("m=%d goods==free4(m-6)=%d" % (m, fc), match)
            ok &= check("m=%d all c6*mu witnessed (exact)" % m, wit_ok)
    _ = Rational  # keep import honest if witnesses short-circuit
    for ln in log:
        print(ln)
    print("check_N6_O1 OK" if ok else "check_N6_O1 FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/O1.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N6_O1 OK" if ok
                       else "check_N6_O1 FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
