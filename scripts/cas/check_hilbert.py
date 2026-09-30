"""Hilbert-series certificate (exact integer arithmetic, no CAS needed).
H_R(t) = (1-t^28)(1-t^48)/((1-t)^2(1-t^4)(1-t^6)(1-t^14)(1-t^24)(1-t^46)).
Checks (all exact):
  H1. anchors [t^46]=1519, [t^47]=1626, [t^48]=1745 (closure boundary).
  H2. H_R == 3-family F-module pattern for 0<=w<=83.
  H3. divergence table 84..100 (new directions; 4th family onward).
  H4. F46*H*F0-layer fit (K/(p^2) counts) for 84..91 [conditional on run].
Prints PASS/FAIL plus `hilbert OK` (exit 0/1).
Run: python3 scripts/cas/check_hilbert.py  # log: data/hilbert.log
"""
import sys

GW6 = (1, 1, 6, 4, 14, 24)
GWK = (1, 1, 6, 4)


def count(W, G):
    if W < 0:
        return 0
    n = 0

    def rec(i, rem):
        nonlocal n
        if i == len(G) - 1:
            if rem % G[i] == 0:
                n += 1
            return
        for e in range(rem // G[i] + 1):
            rec(i + 1, rem - e * G[i])
    rec(0, W)
    return n


s6 = lambda w: count(w, GW6)  # noqa: E731
sK = lambda w: count(w, GWK)  # noqa: E731
N = 100
num = [0] * (N + 1)
num[0] = 1
num[28] -= 1
num[48] -= 1
num[76] += 1
from collections import defaultdict
D = defaultdict(int)
D[0] = 1
for e in (1, 1, 4, 6, 14, 24, 46):
    ND = defaultdict(int)
    for k, v in D.items():
        ND[k] += v
        ND[k + e] -= v
    D = ND
D = dict(D)
H = [0] * (N + 1)
for n in range(N + 1):
    s = num[n]
    for k, v in D.items():
        if 0 < k <= n:
            s -= v * H[n - k]
    H[n] = s


def Pmod(w):
    return ((s6(w) - s6(w - 28)) + (sK(w - 46) - sK(w - 48))
            + (sK(w - 60) - sK(w - 62)) + (sK(w - 70) - sK(w - 72)))


fails = []


def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name +
          ((" [" + str(detail) + "]") if detail else ""))
    if not cond:
        fails.append(name)


check("H1 anchors 1519/1626/1745",
      H[46] == 1519 and H[47] == 1626 and H[48] == 1745,
      (H[46], H[47], H[48]))
check("H2 match 3-family 0..83",
      all(H[w] == Pmod(w) for w in range(84)))
Dtab = [(w, H[w] - Pmod(w)) for w in range(84, 101)]
check("H3 divergence starts at 84 with +1",
      Dtab[0] == (84, 1) and all(d > 0 for _, d in Dtab[1:]),
      Dtab[:6])
# H4: F46*H*F0*K/(p^2) layer accounts for 84..91 exactly
check("H4 fourth family fits 84..91",
      [H[w] - Pmod(w) for w in range(84, 92)] ==
      [sK(w - 84) - sK(w - 86) for w in range(84, 92)])
print("D-table 84..100:", [(w, H[w] - Pmod(w)) for w in range(84, 101)])

if fails:
    print("hilbert FAILED:", fails)
    sys.exit(1)
print("hilbert OK")
