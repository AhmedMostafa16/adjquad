"""W-expansion valuation profile of the weight-46 witness + non-membership.

Reads data/witness_w46.txt (integral 79-term F). Computes exact QQ
W-expansion F = sum H_j W^j (a0-descent with rho=G0/c) and p/q valuations
of each H_j vs the P/R2/Q-top bounds. Also reduces F mod p by the C5-span
RREF: nonzero residual => F outside C5-span over QQ (rigorous).

Run: python3 scripts/cas/profile_witness.py
Writes: data/profile_witness.log
"""

from collections import defaultdict
from fractions import Fraction
import sys
sys.path.insert(0, "scripts/cas")
from check_s6 import mono_w, PRIME
from sympy import Poly, Rational, expand, symbols, together, fraction, cancel

W = 46
a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
p, q = a4, a5
J1 = 2 * a1 * a4 - a2**2
J2 = 2 * a2 * a5 - a3**2
F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
      + Rational(1, 3) * a4 * a5**2 * a3**3 * a1
      + Rational(1, 3) * a5**2 * a3**3 * a2**2
      - Rational(1, 5) * a5 * a3**5 * a2 + Rational(1, 35) * a3**7)
c = a4**2 * a5**4
G0 = expand(F0 - c * a0)
rho = together(G0 / c)

terms = []
with open("data/witness_w46.txt") as fh:
    for line in fh:
        parts = line.strip().split()
        ex = tuple(map(int, parts[0].split(",")))
        terms.append((int(parts[1]), ex))
F = sum(co * a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3] * a4**e[4] * a5**e[5]
        for co, e in terms)
F = expand(F)
print("terms =", len(terms), flush=True)

# D(F) = 0 exact check
D = lambda m: sum(m[i] * a0**0 for i in [])  # placeholder
HD = defaultdict(int)
for e, cc in Poly(F, a0, a1, a2, a3, a4, a5).as_dict().items():
    for i in range(4):
        if e[i]:
            t = list(e)
            t[i] -= 1
            t[i + 1] += 1
            t[i + 2] += 1
            HD[tuple(t)] += int(cc) * e[i]
print("D(F)==0 exactly:", all(v == 0 for v in HD.values()), flush=True)

PF = Poly(F, a0)
a0deg = PF.degree()
print("a0-degree =", a0deg, flush=True)
C = {k: expand(PF.nth(k)) for k in range(a0deg + 1)}

# W-descent: H_m = C_m; H_k = C_k - sum_{j>k} binom(j,k) H_j rho^{j-k}
from sympy import binomial
Hc = {}
for k in range(a0deg, -1, -1):
    s = C[k]
    for j in range(k + 1, a0deg + 1):
        s = s - binomial(j, k) * Hc[j] * rho**(j - k)
    Hc[k] = together(s)
    print("H_%d computed" % k, flush=True)


def vpq(e):
    n, d = fraction(together(e))
    n, d = expand(n), expand(d)
    op = lambda ee, v: min(Poly(ee, v).as_dict(), key=lambda t: t[0])[0] if Poly(ee, v).as_dict() else 0
    return op(n, a5) - op(d, a5), op(n, a4) - op(d, a4)


lines = []
lines.append("W-expansion valuations (m=%d):" % a0deg)
for j in range(a0deg + 1):
    vq, vp = vpq(Hc[j])
    iszero = expand(cancel(Hc[j])) == 0
    lines.append("  H_%d: vq=%d vp=%d %s | P/R2 need vp>=%d; Q(q) need vq>=%d"
                 % (j, vq, vp, "(zero)" if iszero else "", 2 * j, 4 * j))
print("\n".join(lines), flush=True)

# lambda values
lams = [(vpq(Hc[j])[0] - 4 * j, vpq(Hc[j])[1] - 2 * j) for j in range(a0deg + 1)
        if expand(cancel(Hc[j])) != 0]
lines.append("min(vq-4j)=%d (R1 needs >=-2m=%d); min(vp-2j)=%d (R2 needs >=0)"
             % (min(l[0] for l in lams), -2 * a0deg, min(l[1] for l in lams)))

# non-membership: reduce F mod p by C5 RREF (reuse fingerprint machinery lightly)
dom = mono_w(W)
ridx = {m: i for i, m in enumerate(dom)}
n = len(dom)


def growdict(poly):
    import math
    pd = Poly(expand(poly), a0, a1, a2, a3, a4, a5).as_dict()
    dens = 1
    for cc in pd.values():
        r = Rational(cc)
        dens = dens * r.q // math.gcd(dens, r.q)
    d = defaultdict(int)
    for ex, cc in pd.items():
        v = Rational(cc) * dens
        assert v.q == 1
        d[ridx[ex]] = (d[ridx[ex]] + int(v.p)) % PRIME
    return d


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
                    gd = growdict(expand(base * (p**a_) * (q**(r3 - a_))))
                    if any(gd.values()):
                        grows.append(gd)
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
    inv = pow(G[grow][c] % PRIME, PRIME - 2, PRIME)
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
gpivrow = {c: G[i] for i, c in enumerate(gcols)}
Fbar = defaultdict(int)
for co, ex in terms:
    Fbar[ridx[ex]] = (Fbar[ridx[ex]] + co) % PRIME
r = dict(Fbar)
for c in gcols:
    f = r.get(c, 0) % PRIME
    if f == 0:
        continue
    r.pop(c, None)
    for cc, vv in gpivrow[c].items():
        r[cc] = (r.get(cc, 0) - f * vv) % PRIME
        if r[cc] == 0:
            del r[cc]
res = {k: v for k, v in r.items() if v % PRIME != 0}
lines.append("residual of F mod (p, C5-span): %d terms (nonzero => F outside C5 over QQ)" % len(res))
print(lines[-1], flush=True)
with open("data/profile_witness.log", "w") as fh:
    fh.write("\n".join(lines) + "\n")
