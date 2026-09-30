"""Exact six-generator N=5 invariant ring + lemma refutations (check_s6).

SymPy-only + stdlib.  Dictionary: x=a3, y=a2, z=a1, p=a4, q=a5; J1=2pz-y2,
J2=2qy-x2; D(x)=pq, D(y)=px, D(z)=xy; F0=p2 q4 a0 - pq3 xyz + (1/3)pq2 x3 z
+ (1/3)q2 x3 y2 - (1/5) qx5 y + (1/35) x7; c=p2 q4; W=F0/c.

Checks (PASS/FAIL each, final `check_s6 OK`, exit 0/1):
  A. S = q4 H - 11025 F0^2 - 105 q2 J2^5 J1 - 9 J2^7 = 0 in k[a0..a5] (H the
     17-term wt-24 invariant; also D(H) = 0 by direct computation).
  B. S irreducible in the free 6-gen ring (weights 1,1,6,4,14,24), weight 28.
  C. H = H2 W2 + H0,  H2=11025p4q4, H1=0, H0=105J2^5J1/q2+9J2^7/q4;
     p/q valuations vs bounds  (vp >= 2j, vq >= 4j): Q broken at j=0,2
     (H1=0); P holds (vp(H2)=4=4, vp(H0)=0=0).
  D. C0 = H0 + H1 rho + H2 rho2 a genuine polynomial; q^-4 pole cancels
     (q4(H2 rho2) -> +9 x14, q4 H0 -> -9 x14 mod q): r_q^2 in L_q.
  E. N(w) = dim ker(D|V_w) over F_1000003 equals s6(w) - s6(w-28); Hilbert
     series (1-t28)/((1-t)^2(1-t4)(1-t6)(1-t14)(1-t24)).

Run:  python3 scripts/cas/check_s6.py  # log: data/s6.log
"""

from collections import defaultdict
from sympy import (Poly, Rational, factor, fraction, together, expand,
                  symbols, Mul, Pow, cancel)

PRIME = 1000003
TESTW = [5, 15, 23, 24, 25, 30, 35, 40]
log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


# ---------------- symbols and explicit objects (a0..a5) ----------------
a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
J1 = 2 * a1 * a4 - a2**2
J2 = 2 * a2 * a5 - a3**2
c = a4**2 * a5**4
F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
      + Rational(1, 3) * a4 * a5**2 * a3**3 * a1
      + Rational(1, 3) * a5**2 * a3**3 * a2**2
      - Rational(1, 5) * a5 * a3**5 * a2 + Rational(1, 35) * a3**7)
G0 = expand(F0 - c * a0)
rho = together(G0 / c)
# H: the 17-term wt-24 invariant verbatim from Counterexample.lean,
# monomials listed as (coeff, [a0,a1,a2,a3,a4,a5] exponents).
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


def _mk(e):
    return a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3] * a4**e[4] * a5**e[5]


H = sum(co * _mk(ex) for (co, ex) in HMONO)

# Exact W-expansion (C1 = 22050 a4^2 G0 forces H1 = 0):
#     H = 11025 p^4 q^4 W^2 + (105 J2^5 J1/q^2 + 9 J2^7/q^4)
H2 = 11025 * a4**4 * a5**4             # vq=4, vp=4  (top coefficient)
H1 = 0                                 # 0 (no W^1 term: C1 = 2 H2 rho exactly)
H0 = 105 * J2**5 * J1 / a5**2 + 9 * J2**7 / a5**4   # vq=-4, vp=0


def ordp(e, v):
    e = expand(e)
    d = Poly(e, v).as_dict()
    return min(t[0] for t in d) if d else 0


def vpq(e):
    n, d = fraction(together(e))
    n, d = expand(n), expand(d)
    return ordp(n, a5) - ordp(d, a5), ordp(n, a4) - ordp(d, a4)


def mono_w(w):
    res = []
    for e0 in range(w // 8 + 1):
        r0 = w - 8 * e0
        for e1 in range(r0 // 5 + 1):
            r1 = r0 - 5 * e1
            for e2 in range(r1 // 3 + 1):
                r2 = r1 - 3 * e2
                for e3 in range(r2 // 2 + 1):
                    rem = r2 - 2 * e3
                    for e4 in range(rem + 1):
                        res.append((e0, e1, e2, e3, e4, rem - e4))
    return res


def Dmono(m):
    out = defaultdict(int)
    for i in range(4):
        if m[i]:
            t = list(m)
            t[i] -= 1
            t[i + 1] += 1
            t[i + 2] += 1
            out[tuple(t)] += m[i]
    return {k: v for k, v in out.items() if v}


_s6memo = {}


def s6(w):
    if w < 0:
        return 0
    if w in _s6memo:
        return _s6memo[w]
    dp = [0] * (w + 1)
    dp[0] = 1
    for _ in (0, 1):                    # two weight-1 types
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s + 1):
                ndp[s] += dp[s - e]
        dp = ndp
    for coin in (6, 4, 14, 24):
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s // coin + 1):
                ndp[s] += dp[s - e * coin]
        dp = ndp
    _s6memo[w] = dp[w]
    return dp[w]


_nullmemo = {}


def nullity(w):
    if w in _nullmemo:
        return _nullmemo[w]
    dom = mono_w(w)
    n = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    M = [defaultdict(int) for _ in range(n)]
    for colj, mm in enumerate(dom):
        for nm, k in Dmono(mm).items():
            r = ridx.get(nm)
            if r is not None:
                M[r][colj] = (M[r][colj] + k) % PRIME
    rank = 0
    for ccol in range(n):
        pv = None
        for r in range(rank, n):
            if M[r].get(ccol, 0) != 0:
                pv = r
                break
        if pv is None:
            continue
        M[rank], M[pv] = M[pv], M[rank]
        lead = M[rank][ccol]
        inv = pow(lead, PRIME - 2, PRIME)
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
    res = n - rank
    _nullmemo[w] = res
    return res


def main():
    ok = True

    # A. S = 0 and D(H) = 0.
    S = expand(a5**4 * H - 11025 * F0**2
               - 105 * a5**2 * J2**5 * J1 - 9 * J2**7)
    ok &= check("A-S-is-zero", expand(S) == 0)
    HD = defaultdict(int)
    for e, cc in Poly(H, a0, a1, a2, a3, a4, a5).as_dict().items():
        for nm, k in Dmono(e).items():
            HD[nm] += int(cc) * k
    ok &= check("A-DH-zero", all(v == 0 for v in HD.values()))

    # B. S irreducible + weight 28 (free 6-var ring).
    P1, P2, R1, R2, R5, H6 = symbols("P Q R1 R2 R5 H6")
    Sfree = P2**4 * H6 - 11025 * R5**2 - 105 * P2**2 * R2**5 * R1 - 9 * R2**7
    wgt = {P1: 1, P2: 1, R1: 6, R2: 4, R5: 14, H6: 24}

    def tw(t):
        if isinstance(t, Mul):
            return sum(tw(f) for f in t.args)
        if isinstance(t, Pow):
            return wgt.get(t.base, 0) * int(t.exp)
        return wgt.get(t, 0)

    ok &= check("B-Sfree-weight-28",
                max(tw(t) for t in expand(Sfree).as_ordered_terms()) == 28)
    ok &= check("B-Sfree-irreducible", factor(Sfree) == Sfree)
    ok &= check("B-Sfree-deg-H6-one", Poly(Sfree, H6).degree() == 1)
    log.append("  factor(Sfree) = " + str(factor(Sfree)))

    # C. W-coefficients vs the saturation bounds.  H1 = 0, so the p-lemma
    #    vp >= 2j holds (vp(H2)=4=4, vp(H0)=0=0) but the q-lemma vq >= 4j
    #    breaks at j=2 (vq(H2)=4<8) and j=0 (vq(H0)=-4<0).  q-lemma refutes,
    #    p-lemma does not.
    vq2, vp2 = vpq(H2)
    vq0, vp0 = vpq(H0)
    log.append("  valuations  H2 vp=%d vq=%d (2j=4, 4j=8)  |  "
               "H0 vp=%d vq=%d (2j=0, 4j=0)  |  H1 = 0" %
               (vp2, vq2, vp0, vq0))
    ok &= check("C-H2-in-Kpq", H2.has(a0) == False)
    ok &= check("C-H1-is-zero", H1 == 0)
    ok &= check("C-q-refuted-j2-H2", vq2 < 8)
    ok &= check("C-q-refuted-j0-H0", vq0 < 0)
    ok &= check("C-p-sat-j2-H2", vp2 >= 4)
    ok &= check("C-p-sat-j0-H0", vp0 >= 0)

    # D. C0 = [a0^0] H (genuine) = H2 rho^2 + H0; kill shot: the q^-4 pole
    #    cancels (q^4(H2 rho^2) -> +9 x^14, q^4 H0 -> -9 x^14 mod q): r_q^2
    #    is algebraic over L_q, not transcendental (rem:q-obstacle).
    C0 = expand(Poly(H, a0).nth(0))
    cq, cp = vpq(C0)
    log.append("  C0 valuations vp=%d vq=%d  (genuine: must be >= 0)"
               % (cp, cq))
    ok &= check("D-C0-genuine-vq", cq >= 0)
    ok &= check("D-C0-genuine-vp", cp >= 0)
    ok &= check("D-C0-eq-Wexp",
                expand(cancel(together(H0 + H1 * rho + H2 * rho**2)) - C0) == 0)
    killA = expand(cancel(a5**4 * H2 * rho**2).subs(a5, 0))
    killB = expand(cancel(a5**4 * H0).subs(a5, 0))
    log.append("  kill shot  q4(H2 rho2)|q=0 = %s   q4 H0|q=0 = %s"
               % (killA, killB))
    ok &= check("D-killshot-A", killA == 9 * a3**14)
    ok &= check("D-killshot-B", killB == -9 * a3**14)
    ok &= check("D-killshot-sum-0", expand(killA + killB) == 0)

    # E. weighted-dimension identification.
    log.append("E:   w   N(w)   s6(w)-s6(w-28)   match")
    for w in TESTW:
        n = nullity(w)
        t = s6(w) - s6(w - 28)
        log.append("    %-5d %-7d %-18s %s"
                   % (w, n, t, "OK" if n == t else "MISMATCH"))
        ok &= check("E-w%d-N%d" % (w, n), n == t)
    log.append("  anchors N(23)=%d N(24)=%d N(25)=%d (want 188 213 238)"
               % (nullity(23), nullity(24), nullity(25)))
    ok &= check("E-anchor-23-188", nullity(23) == 188)
    ok &= check("E-anchor-24-213", nullity(24) == 213)
    ok &= check("E-anchor-25-238", nullity(25) == 238)

    for ln in log:
        print(ln)
    print("check_s6 OK" if ok else "check_s6 FAILED")
    try:
        import os
        os.makedirs("logs", exist_ok=True)
        with open("data/s6.log", "w") as fh:
            fh.write("\n".join(log +
                               ["check_s6 OK" if ok else "check_s6 FAILED"])
                     + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())