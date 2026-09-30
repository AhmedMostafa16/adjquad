"""N=7 B-level weighted kernel probe (RECON ONLY, first look).

B7 = k[a1..a7], D7(a_i) = a_{i+1}*a_{i+2} for i <= 5, D7(a6) = D7(a7) = 0.
Fibonacci weights (13,8,5,3,2,1,1) for a1..a7. D7 is weight-homogeneous
of degree 0: ker computed per-weight V_w -> V_w (mod-PRIME nullity).
No generator conjecture wired in: GEN_WTS_GUESS is filled by the
Hilbert-fit below (free-product fit on observed kerdims); the a1-ladder
hunt for the top generator is reported separately if found.

By the shift pattern, (B7,D7) ~= (A6,D6) is expected -- hence this
probe inherits A6's openness; it is evidence for Phase 6+/N=7 design.

Run:
    python3 scripts/cas/check_N7_Bweighted.py  # log: data/n7/Bweighted.log
Exit 0 on clean run (any verdict), 1 on crash.
"""

import os
import sys
import time
from collections import defaultdict

WT = [13, 8, 5, 3, 2, 1, 1]  # a1..a7
GEN_WTS_GUESS = [1, 1]  # sinks a6, a7; rest FITTED below, not assumed
W_MAX = 22
PRIME = 1000003


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


def _D7(m):
    out = defaultdict(int)
    # a1->a2a3, ..., a5->a6a7; a6,a7 killed.
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
    if w in _nullmemo:
        return _nullmemo[w]
    dom = _wtuples(w)
    res = _nullity(dom, [_D7(m) for m in dom])
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
    print("w  dimV  kerdim")
    log = ["w  dimV  kerdim"]
    for w in range(W_MAX + 1):
        dom = _wtuples(w)
        kd = kerdim(w)
        line = "  %-3d %-5d %-6d" % (w, len(dom), kd)
        print(line, flush=True)
        log.append(line)
    print("N7-B-WEIGHTED OK (recon only) elapsed=%.1fs"
          % (time.monotonic() - t0))
    try:
        os.makedirs("data/n7", exist_ok=True)
        with open("data/n7/Bweighted.log", "w") as fh:
            fh.write("\n".join(log + ["N7-B-WEIGHTED OK"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
