"""Mod-p tower sweep 58-75 (Task 5 time-box step).

Reuses scripts/cas/hunt_high_weights.py pattern VERBATIM: the nullity()
function is imported from hunt_high_weights (same sparse mod-p elimination,
same PRIME=1000003, same mono_w/Dmono/s6 from check_s6). Only the driver
differs: weights 58-75, excess-vs-prediction accounting
  excess(w) = N_modp(w) - (s6(w)-s6(w-28))
  bare(w)   = sK(w-46)-sK(w-48), corr(w) = bare + [w>=60] + [w>=70]
and a per-weight 600s stop rule (time-box: stop the sweep where mod-p
becomes infeasible and report the covered range exactly).

Assumption (checked exactly at 58-60 by tower_hunt.sage, through 57 by
thm:minimal-45): rank(G_w) = s6(w)-s6(w-28) mod p, i.e. no second C5
relation. Any DEVIATION triggers deviation-targeted exact QQ follow-up
(which checks both ranks). Agreement is evidence, not proof.

Run: python3 scripts/cas/sweep_tower_modp.py
Writes: /tmp/opencode/sdd/sweep_modp.log (incremental flush per weight;
tracked data/hunt_high.log is NOT touched).
Appendix archived in data/tower_hunt.log (mod-p sweep appendix, weights 58-69).
Provenance: committed verbatim from /tmp/opencode/sdd/sweep_modp.py
(recovery 2026-09-21; sweep logic unchanged, NOT re-run on commit).
"""

import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
sys.path.insert(0, "scripts/cas")
sys.path.insert(0, "/projects/adjquad/scripts/cas")
from check_s6 import s6  # noqa: E402
from hunt_high_weights import nullity  # noqa: E402  (verbatim pattern reuse)

LOG = "/tmp/opencode/sdd/sweep_modp.log"


def sK(w):
    if w < 0:
        return 0
    dp = [0] * (w + 1)
    dp[0] = 1
    for _ in (0, 1):
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s + 1):
                ndp[s] += dp[s - e]
        dp = ndp
    for coin in (6, 4):
        ndp = [0] * (w + 1)
        for s in range(w + 1):
            for e in range(s // coin + 1):
                ndp[s] += dp[s - e * coin]
        dp = ndp
    return dp[w]


def bare(w):
    return sK(w - 46) - sK(w - 48)


def corr(w):
    return bare(w) + (1 if w >= 60 else 0) + (1 if w >= 70 else 0)


def main():
    with open(LOG, "w") as fh:
        fh.write("# mod-p tower sweep 58-75 [F_1000003, hunt_high_weights.nullity verbatim]\n")
        fh.write("# excess = N_modp - (s6-s6(-28)); bare = sK(w-46)-sK(w-48); "
                 "corr = bare + [w>=60 F.F0] + [w>=70 F.H]\n")
    covered = []
    for w in range(58, 76):
        t0 = time.time()
        n, nul = nullity(w)
        dt = time.time() - t0
        f = s6(w) - s6(w - 28)
        b, c = bare(w), corr(w)
        exc = nul - f
        if exc == b:
            v = "MATCH-bare"
        elif exc == c:
            v = "MATCH-F-product"
        else:
            v = "DEVIATION-needs-exact"
        line = ("w=%d dimV=%d Nmod=%d formula=%d bare=%d corr=%d excess=%d %s (%.1fs)"
                % (w, n, nul, f, b, c, exc, v, dt))
        print(line, flush=True)
        with open(LOG, "a") as fh:
            fh.write(line + "\n")
        covered.append(w)
        if dt > 600:
            stop = ("STOP: per-weight 600s budget exceeded at w=%d; "
                    "sweep covers 58-%d" % (w, w))
            print(stop, flush=True)
            with open(LOG, "a") as fh:
                fh.write(stop + "\n")
            break
    done = "# sweep done: covered 58-%d" % covered[-1]
    print(done, flush=True)
    with open(LOG, "a") as fh:
        fh.write(done + "\n")


if __name__ == "__main__":
    main()
