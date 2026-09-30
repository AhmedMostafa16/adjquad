"""N=6 weighted kernel check.

B = k[a_1..a_6], D_6(a_1)=a_2a_3, D_6(a_2)=a_3a_4, D_6(a_3)=a_4a_5,
D_6(a_4)=a_5a_6, D_6(a_5)=D_6(a_6)=0, Fibonacci weights (8,5,3,2,1,1).

D preserves Fibonacci weight, so ker is computed per weight V_w -> V_w.
Mod-PRIME nullity on exponent tuples, cross-checked against the exact-QQ
SageMath oracle (data/n6/axis1_sage_probe.log). D(G_i)=0 plus algebraic
independence (Jacobian minor 420*a_5^3*a_6^5) give span = ker when
kerdim equals the free count.

Kerdims match the free five-generator count through w = 23, then the
hypersurface count s6(w) - s6(w-28) from w = 24 through w = 32
(paper/10-n6.tex).

Run: python3 scripts/cas/check_N6_weighted_v2.py
"""

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import verify_D  # noqa: E402

WT = [8, 5, 3, 2, 1, 1]  # a_1..a_6
GEN_WTS = [1, 1, 4, 6, 14]  # G_1..G_5
HYP_WTS = [1, 1, 4, 6, 14, 24]  # plus H_B (Theorem thm:n6-hypersurface)
W_MAX = 32
PRIME = 1000003

# Exact-QQ SageMath oracle (data/n6/axis1_sage_probe.log), w = 0..20.
ORACLE = [1, 2, 3, 4, 6, 8, 11, 14, 18, 22, 27, 32, 39, 46, 55, 64, 75,
          86, 100, 114, 131]

log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def _mono_w(w):
    """Exponent tuples of B of exact Fibonacci weight w."""
    out = []

    def rec(idx, left, cur):
        if idx == 6:
            if left == 0:
                out.append(tuple(cur))
            return
        v = WT[idx]
        for e in range(left // v + 1):
            rec(idx + 1, left - v * e, cur + [e])

    rec(0, w, [])
    return out


def dimV(w):
    return len(_mono_w(w))


def _Dmono(m):
    """D_6 on an exponent tuple; image tuples keep weight w (Fibonacci)."""
    out = defaultdict(int)
    # (source, targets): a1->a2a3, a2->a3a4, a3->a4a5, a4->a5a6.
    for i, (t1, t2) in enumerate(((1, 2), (2, 3), (3, 4), (4, 5))):
        if m[i]:
            t = list(m)
            t[i] -= 1
            t[t1] += 1
            t[t2] += 1
            out[tuple(t)] += m[i]
    return {k: v for k, v in out.items() if v}


_nullmemo = {}


def kerdim(w):
    """dim ker(D_6 : V_w -> V_w) over F_PRIME."""
    if w in _nullmemo:
        return _nullmemo[w]
    dom = _mono_w(w)
    n = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    M = [defaultdict(int) for _ in range(n)]
    for colj, mm in enumerate(dom):
        for nm, k in _Dmono(mm).items():
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
    _nullmemo[w] = n - rank
    return n - rank


_fcmemo = {}


def free_count(degs, w):
    """Monomial count of weight w in generators of weights degs."""
    key = (tuple(degs), w)
    if key in _fcmemo:
        return _fcmemo[key]
    if w < 0:
        return 0
    if not degs:
        return 1 if w == 0 else 0
    first, rest = degs[0], degs[1:]
    s = sum(free_count(rest, w - first * e) for e in range(w // first + 1))
    _fcmemo[key] = s
    return s


def hyp_count(w):
    """Hypersurface count s6(w) - s6(w-28) on HYP_WTS (single wt-28
    relation; exact while S_B generates all relations through w)."""
    return free_count(HYP_WTS, w) - free_count(HYP_WTS, w - 28)


def _generators(a):
    a1, a2, a3, a4, a5, a6 = a[1], a[2], a[3], a[4], a[5], a[6]
    G1 = a5
    G2 = a6
    G3 = 2 * a2 * a5 - a3**2
    G4 = 2 * a3 * a6 - a4**2
    G5 = (105 * a1 * a5**2 * a6**4
          - 105 * a2 * a3 * a4 * a5 * a6**3
          + 35 * a2 * a4**3 * a5 * a6**2
          + 35 * a3**2 * a4**3 * a6**2
          - 21 * a3 * a4**5 * a6
          + 3 * a4**7)
    return [G1, G2, G3, G4, G5]


def main():
    from sympy import expand, symbols

    ok = True
    N = 6
    a = symbols("a_0:7")
    names = ["G_1=a_5", "G_2=a_6", "G_3=2a_2a_5-a_3^2",
             "G_4=2a_3a_6-a_4^2", "G_5 (degree 7)"]
    for name, g in zip(names, _generators(a)):
        ok &= check("D(%s)=0" % name, verify_D(g, a, N) is True)
    G = _generators(a)
    a1, a2, a3, a5, a6 = a[1], a[2], a[3], a[5], a[6]
    det = __import__("sympy").Matrix(
        [[g.diff(c) for c in (a1, a2, a3, a5, a6)] for g in G]).det()
    ok &= check("Jacobian 5x5 minor = 420*a_5^3*a_6^5",
                expand(det - 420 * a5**3 * a6**5) == 0)

    log.append("w  dimV  kerdim  free  hyp   gap")
    for w in range(W_MAX + 1):
        kd = kerdim(w)
        fc = free_count(GEN_WTS, w)
        hc = hyp_count(w)
        log.append("  %-3d %-5d %-6d %-4d %-5d %+d"
                   % (w, dimV(w), kd, fc, hc, kd - fc))
        if w <= 20:
            oc = ORACLE[w]
            ok &= check("w=%d kerdim==free==oracle(%d)" % (w, oc),
                        kd == fc == oc == hc)
        elif w <= 23:
            ok &= check("w=%d kerdim==free==hyp(%d)" % (w, hc),
                        kd == fc == hc)
        else:
            ok &= check("w=%d kerdim==hyp(%d)" % (w, hc), kd == hc)
    for ln in log:
        print(ln)
    print("check_N6_weighted_v2 OK" if ok else "check_N6_weighted_v2 FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/weighted_v2.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N6_weighted_v2 OK" if ok
                       else "check_N6_weighted_v2 FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
