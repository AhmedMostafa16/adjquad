"""Extended dimension hunt: kernel dims vs six-generator hypersurface formula.

Compares N(w) = dim ker(D5|V_w) over F_1000003 against s6(w)-s6(w-28)
for weights beyond the manuscript frontier (41+). Any MISMATCH is a
potential second hidden generator (falsifier for Conj 11.2); agreement
extends the evidence and sharpens the hunt bound.

Usage: python3 scripts/cas/hunt_high_weights.py [wmin] [wmax]
Default: 41 56. Prints timing per weight. Writes data/hunt_high.log.
"""

import sys
import time
from collections import defaultdict

sys.path.insert(0, "scripts/cas")
from check_s6 import mono_w, Dmono, s6, PRIME

def nullity(w):
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
    return n, n - rank


def main():
    wmin = int(sys.argv[1]) if len(sys.argv) > 1 else 41
    wmax = int(sys.argv[2]) if len(sys.argv) > 2 else 56
    lines = []
    ok = True
    for w in range(wmin, wmax + 1):
        t0 = time.time()
        n, nul = nullity(w)
        t = s6(w) - s6(w - 28)
        match = (nul == t)
        ok &= match
        line = "w=%d dimV=%d N=%d formula=%d %s (%.1fs)" % (
            w, n, nul, t, "OK" if match else "MISMATCH", time.time() - t0)
        print(line, flush=True)
        lines.append(line)
    lines.append("HUNT " + ("OK" if ok else "MISMATCH-FOUND"))
    with open("data/hunt_high.log", "w") as fh:
        fh.write("\n".join(lines) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
