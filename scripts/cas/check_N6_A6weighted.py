"""N=6 full-ring (A6) weighted kernel probe: H^(6) hunt (evidence only).

A6 = k[a0..a6], D6(a0) = a1a2 (rest as in check_N6_kernel.py),
Fibonacci weights WT = (13,8,5,3,2,1,1). D6 is weight-homogeneous of
degree 0, so ker is computed per-weight V_w -> V_w (mod-PRIME nullity
on exponent tuples). Compared against the free ring on the five
B-generators (weights 1,1,4,6,14) plus F0_6 (weight 25,
scripts/cas/check_N6_F0.py): gap > 0 at weight w is a hidden
A6-generator at w (the H-analog); gap < 0 is an alarm (dependence).

Span equality is NOT checked; this is RECON-only evidence.
Caveat (Theorem thm:n6-hypersurface): from weight 24 the gap mixes
the B-level hypersurface excess (+1,+2,...) with genuine a0-content;
subtract the known B-contribution first (Lemma lem:n6-H20 does this
at weight 20, where the B-level is exact). Global A6-generation
stays Open.

Run:
    python3 scripts/cas/check_N6_A6weighted.py  # log: data/n6/A6weighted.log
Exit 0 on clean run (any verdict), 1 on crash. Also writes the table to
data/n6/A6weighted.log.
"""

import os
import sys
import time
from collections import defaultdict

WT = [13, 8, 5, 3, 2, 1, 1]  # a0..a6
GEN_WTS = [1, 1, 4, 6, 14, 25]  # G1..G5, F0_6
W_MAX = 30
PRIME = 1000003

log = []


def _wtuples(w):
    out = []

    def rec(idx, left, cur):
        if idx == 7:
            if left == 0:
                out.append(tuple(cur))
            return
        v = WT[idx]
        for e in range(left // v + 1):
            rec(idx + 1, left - v * e, cur + [e])

    rec(0, w, [])
    return out


def _D6(m):
    out = defaultdict(int)
    # a0->a1a2, a1->a2a3, a2->a3a4, a3->a4a5, a4->a5a6.
    for i, (t1, t2) in enumerate(((1, 2), (2, 3), (3, 4), (4, 5), (5, 6))):
        if m[i]:
            t = list(m)
            t[i] -= 1
            t[t1] += 1
            t[t2] += 1
            out[tuple(t)] += m[i]
    return {k: v for k, v in out.items() if v}


def _nullity(rows, cols):
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


_nullmemo = {}


def kerdim(w):
    """dim ker(D6 : V_w -> V_w) over F_PRIME (A6, wt(a0) = 13)."""
    if w in _nullmemo:
        return _nullmemo[w]
    dom = _wtuples(w)
    res = _nullity(dom, [_D6(m) for m in dom])
    _nullmemo[w] = res
    return res


_fcmemo = {}


def free_count(degs, w):
    if w < 0:
        return 0
    if not degs:
        return 1 if w == 0 else 0
    key = (tuple(degs), w)
    if key in _fcmemo:
        return _fcmemo[key]
    first, rest = degs[0], degs[1:]
    s = sum(free_count(rest, w - first * e) for e in range(w // first + 1))
    _fcmemo[key] = s
    return s


def main():
    t0 = time.monotonic()
    print("w  dimV  kerdim  free  gap")
    log.append("w  dimV  kerdim  free  gap")
    hidden = []
    for w in range(W_MAX + 1):
        dom = _wtuples(w)
        kd = kerdim(w)
        fc = free_count(GEN_WTS, w)
        gap = kd - fc
        line = "  %-3d %-5d %-6d %-4d %+d" % (w, len(dom), kd, fc, gap)
        print(line, flush=True)
        log.append(line)
        if gap != 0:
            hidden.append((w, gap))
    print("hidden/dependency signals: %s"
          % ([(w, g) for w, g in hidden] or "none through w=%d" % W_MAX))
    log.append("hidden/dependency: %s" % (hidden or "none"))
    print("N6-A6-WEIGHTED OK (evidence only) elapsed=%.1fs"
          % (time.monotonic() - t0))
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/A6weighted.log", "w") as fh:
            fh.write("\n".join(log + ["N6-A6-WEIGHTED OK"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
