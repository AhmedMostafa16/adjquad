"""Mod-p fingerprint of the weight-46 excess direction (v2, fixed).

Fixes: exact denominator clearing (lcm, no int() truncation), correct
RREF + membership, correct kernel-vector verification.

Run: python3 scripts/cas/fingerprint_w46.py
Writes: data/fingerprint_w46.log, data/vbar_w46.txt
"""

from collections import defaultdict
from fractions import Fraction
import sys
sys.path.insert(0, "scripts/cas")
from check_s6 import mono_w, Dmono, PRIME

W = 46
dom = mono_w(W)
n = len(dom)
ridx = {m: i for i, m in enumerate(dom)}
print("dimV =", n, flush=True)

M = [defaultdict(int) for _ in range(n)]
for j, m in enumerate(dom):
    for im, k in Dmono(m).items():
        r = ridx.get(im)
        if r is not None:
            M[r][j] = (M[r][j] + k) % PRIME

pivcol_of_row = {}
row_of_pivcol = {}
rank = 0
for c in range(n):
    pv = None
    for r in range(rank, n):
        if M[r].get(c, 0) != 0:
            pv = r
            break
    if pv is None:
        continue
    M[rank], M[pv] = M[pv], M[rank]
    lead = M[rank][c]
    inv = pow(lead, PRIME - 2, PRIME)
    for cc in list(M[rank]):
        M[rank][cc] = (inv * M[rank][cc]) % PRIME
    for r in range(n):
        if r == rank:
            continue
        f = M[r].get(c, 0)
        if f == 0:
            continue
        for cc, vv in list(M[rank].items()):
            M[r][cc] = (M[r].get(cc, 0) - f * vv) % PRIME
            if M[r][cc] == 0:
                del M[r][cc]
    M[rank].pop(c, None)
    pivcol_of_row[rank] = c
    row_of_pivcol[c] = rank
    rank += 1
print("rank =", rank, "nullity =", n - rank, flush=True)
pivset = set(row_of_pivcol)
free = [c for c in range(n) if c not in pivset]


def ker_vec(fcol):
    v = {fcol: 1}
    for pc, r in row_of_pivcol.items():
        c = M[r].get(fcol, 0) % PRIME
        if c:
            v[pc] = (-c) % PRIME
    return v


def ker_check(v):
    # row r<rank: v[piv] + sum_stored M[r][j] v[j] == 0; row r>=rank: all-zero row, ok
    for r, pc in pivcol_of_row.items():
        s = v.get(pc, 0) % PRIME
        for cc, vv in M[r].items():
            s = (s + vv * v.get(cc, 0)) % PRIME
        if s != 0:
            return False
    return True


# ---- C5 rows over Fp with EXACT denominator clearing ----
from sympy import Poly, Rational, expand, symbols
a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
J1 = 2 * a1 * a4 - a2**2
J2 = 2 * a2 * a5 - a3**2
F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
      + Rational(1, 3) * a4 * a5**2 * a3**3 * a1
      + Rational(1, 3) * a5**2 * a3**3 * a2**2
      - Rational(1, 5) * a5 * a3**5 * a2 + Rational(1, 35) * a3**7)
HMONO = [((11025), [2, 0, 0, 0, 4, 4]),
         ((-22050), [1, 1, 1, 1, 3, 3]),
         ((7350), [1, 1, 0, 3, 3, 2]),
         ((7350), [1, 0, 2, 3, 2, 2]),
         ((-4410), [1, 0, 1, 5, 2, 1]),
         ((630), [1, 0, 0, 7, 2, 0]),
         ((11025), [0, 2, 2, 2, 2, 2]),
         ((-7350), [0, 2, 1, 4, 2, 1]),
         ((1225), [0, 2, 0, 6, 2, 0]),
         ((6720), [0, 1, 5, 0, 1, 3]),
         ((-16800), [0, 1, 4, 2, 1, 2]),
         ((9450), [0, 1, 3, 4, 1, 1]),
         ((-1540), [0, 1, 2, 6, 1, 0]),
         ((-2208), [0, 0, 7, 0, 0, 3]),
         ((4368), [0, 0, 6, 2, 0, 2]),
         ((-2352), [0, 0, 5, 4, 0, 1]),
         ((385), [0, 0, 4, 6, 0, 0])]
H = sum(co * a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3] * a4**e[4] * a5**e[5]
        for co, e in HMONO)
p, q = a4, a5


def growdict(poly):
    # exact: scale by lcm of denominators, verify integrality
    pd = Poly(expand(poly), a0, a1, a2, a3, a4, a5).as_dict()
    dens = 1
    for cc in pd.values():
        r = Rational(cc)
        dens = dens * r.q // __import__("math").gcd(dens, r.q)
    d = defaultdict(int)
    for ex, cc in pd.items():
        v = Rational(cc) * dens
        assert v.q == 1, ("nonintegral", ex, cc, dens)
        d[ridx[ex]] = (d[ridx[ex]] + int(v.p)) % PRIME
    return d


grows = []
for f in range(W // 24 + 1):
    r0 = W - 24 * f
    for e in range(r0 // 14 + 1):
        Fe = expand(F0**e)
        r1 = r0 - 14 * e
        for d_ in range(r1 // 4 + 1):
            r2 = r1 - 4 * d_
            for c_ in range(r2 // 6 + 1):
                r3 = r2 - 6 * c_
                base = expand((J1**c_) * (J2**d_) * Fe * (H**f))
                for a_ in range(r3 + 1):
                    mon = expand(base * (p**a_) * (q**(r3 - a_)))
                    gd = growdict(mon)
                    if any(gd.values()):
                        grows.append(gd)
print("C5 rows =", len(grows), flush=True)

# RREF of G (rows), collect pivots
G = [dict(g) for g in grows]
gcols = []
grow = 0
for c in sorted({c for g in G for c in g}):
    pv = None
    for r in range(grow, len(G)):
        if G[r].get(c, 0) % PRIME != 0:
            pv = r
            break
    if pv is None:
        continue
    G[grow], G[pv] = G[pv], G[grow]
    lead = G[grow][c] % PRIME
    inv = pow(lead, PRIME - 2, PRIME)
    for cc in list(G[grow]):
        G[grow][cc] = (G[grow][cc] * inv) % PRIME
    for r in range(len(G)):
        if r == grow:
            continue
        f = G[r].get(c, 0) % PRIME
        if f == 0:
            continue
        for cc, vv in list(G[grow].items()):
            G[r][cc] = (G[r].get(cc, 0) - f * vv) % PRIME
            if G[r][cc] == 0:
                del G[r][cc]
    G[grow].pop(c, None)
    gcols.append(c)
    grow += 1
print("rank(G) mod p =", grow, flush=True)
Grow = G[:grow]
gpivrow = {}
for idx, c in enumerate(gcols):
    gpivrow[c] = Grow[idx]


def reduce_by_G(v):
    r = dict(v)
    for c in gcols:
        f = r.get(c, 0) % PRIME
        if f == 0:
            continue
        prow = gpivrow[c]
        r.pop(c, None)  # pivot row has implicit 1 at c (popped during RREF)
        for cc, vv in prow.items():
            r[cc] = (r.get(cc, 0) - f * vv) % PRIME
            if r[cc] == 0:
                del r[cc]
        # pivot col c must now be gone
        assert r.get(c, 0) % PRIME == 0
    return r


# sanity: every C5 row reduces to 0
for gd in grows:
    assert not reduce_by_G(gd), "C5 row not in span!"
print("sanity: all C5 rows reduce to 0 OK", flush=True)

found = None
tried = 0
for fcol in free:
    tried += 1
    v = ker_vec(fcol)
    assert ker_check(v), ("bad ker vec", fcol)
    red = reduce_by_G(v)
    if red:
        found = (fcol, v, red)
        break
print("free cols tried:", tried, "found:", found is not None, flush=True)
lines = []
if found:
    fcol, v, red = found
    nz = sorted((i, x % PRIME) for i, x in v.items() if x % PRIME != 0)
    lines.append("vbar support size = %d" % len(nz))
    from collections import Counter
    prof = Counter(dom[i][0] for i, _ in nz)
    lines.append("vbar a0-profile = %s" % dict(sorted(prof.items())))
    top = max(dom[i][0] for i, _ in nz)
    lines.append("vbar max a0-degree = %d" % top)
    lines.append("vbar top-a0 terms:")
    for i, x in nz:
        if dom[i][0] == top:
            lines.append("  %s : %d" % (dom[i], x))
    lines.append("vbar residual-after-G support = %d" % len(red))
    with open("data/vbar_w46.txt", "w") as fh:
        for i, x in nz:
            fh.write("%s %d\n" % (",".join(map(str, dom[i])), x))
print("\n".join(lines), flush=True)
with open("data/fingerprint_w46.log", "w") as fh:
    fh.write("\n".join(lines) + "\n")
