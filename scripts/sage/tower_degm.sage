"""Degree-m top census vs J_m over exact QQ (Sage).

For fixed a0-degree m with J_m = (p^JP q^JQ):
  N_le(m,w) = nullity of D5 on V_w^{a0<=m}      (direct restricted matrix)
  N_J(m,w)  = nullity of the J_m-constrained a0-chain
              (top C_m parametrized as p^JP q^JQ * u, u in B_{w-8m-JP-JQ})
Violation <=> N_J < N_le  (some kernel vector has a0-degree-m top outside J_m).
N_viol(m,w) = N_le - N_J is compared against the F-module bracket prediction:
  m=4: s_K(w-46) - s_K(w-48)      (F46 family)
  m=5: s_K(w-60) - s_K(w-62)      (F46.F0 family)
  m=6: s_K(w-70) - s_K(w-72)      (F46.H family)
Excess over prediction => NEW PRIMITIVE (escalate).  Deficit => extra torsion.
Matches thm:quotient-4648 at (m=4, w=46,47,48) by construction (1,2,2).

Chain equations (B[a0] freeness): D(C_m) = 0;
  D(C_k) + (k+1)*a1*a2*C_{k+1} = 0, k = 0..m-1.

Born-below-window lemma (paper-level): a primitive a0-degree-m direction
born at w < minC5(m) has top of weight w-8m < minC5(m)-8m = wt(j_m)
(the identity minC5(m)-8m = 2m+4*ceil(m/2) holds for all m by direct
check on e+2r=m), hence top outside J_m.  So the census detects every
gap-born primitive at degree m.

Run: sage scripts/sage/tower_degm.sage m JP JQ w1 [w2 ...] [log=PATH]
Example: sage scripts/sage/tower_degm.sage 5 10 12 60 61 62
"""

import sys
import time
import os

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

# ---------------------------------------------------------------- args
args = [x for x in sys.argv[1:] if not x.startswith("log=")]
LOGPATH = "data/tower_degm.log"
for x in sys.argv[1:]:
    if x.startswith("log="):
        LOGPATH = x[4:]
M = int(args[0]); JP = int(args[1]); JQ = int(args[2])
weights = [int(x) for x in args[3:]]

def Vmons_le(w, dmax):
    res = []
    for e0 in range(min(dmax, w // 8) + 1):
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

def Dcols(m):
    out = {}
    for i in range(4):
        if m[i]:
            t = list(m)
            t[i] -= 1
            t[i + 1] += 1
            t[i + 2] += 1
            t = tuple(t)
            out[t] = out.get(t, 0) + m[i]
    return out

def Bmons5(d):
    res = []
    if d < 0:
        return res
    for e1 in range(d // 5 + 1):
        r1 = d - 5 * e1
        for e2 in range(r1 // 3 + 1):
            r2 = r1 - 3 * e2
            for e3 in range(r2 // 2 + 1):
                rem = r2 - 2 * e3
                for e4 in range(rem + 1):
                    res.append((e1, e2, e3, e4, rem - e4))
    return res

def DcolsB(t):
    out = {}
    for j in range(3):
        if t[j]:
            s = list(t)
            s[j] -= 1
            s[j + 1] += 1
            s[j + 2] += 1
            s = tuple(s)
            out[s] = out.get(s, 0) + t[j]
    return out

def build_chain_mats(w, m, jp, jq, constrained):
    """Blocks B_{w-8k}, k=0..m. constrained: top C_m = p^jp q^jq * u."""
    B = [Bmons5(w - 8 * k) for k in range(m + 1)]
    n = [len(b) for b in B]
    ridx = [{t: i for i, t in enumerate(b)} for b in B]
    U = Bmons5(w - 8 * m - jp - jq) if constrained else B[m]
    s = len(U)
    # column offsets: coff[0]=0 (top, s cols); coff[1] for C_{m-1}; ...
    coff = [0]
    acc = s
    for k in range(m - 1, -1, -1):
        coff.append(acc)
        acc += n[k]
    ncols = acc
    # row offsets: roff[j] starts E_{m-j}: roff[0]=0 (E_m), roff[1]=n[m] (E_{m-1}), ...
    roff = [0]
    acc = 0
    for k in range(m, 0, -1):
        acc += n[k]
        roff.append(acc)
    nrows = acc + n[0]
    Dd = {}
    def add(r, c, v):
        if v:
            Dd[(r, c)] = Dd.get((r, c), 0) + v
    # top block col 0, equation E_m (row block 0): D(C_m) = 0
    if constrained:
        for j, u in enumerate(U):
            mu = (u[0], u[1], u[2], u[3] + jp, u[4] + jq)
            for im, k in DcolsB(mu).items():
                add(roff[0] + ridx[m][im], coff[0] + j, k)
            ku = (u[0] + 1, u[1] + 1, u[2], u[3] + jp, u[4] + jq)
            assert ku in ridx[m - 1], (w, ku)
            add(roff[1] + ridx[m - 1][ku], coff[0] + j, m)
    else:
        for j, t in enumerate(U):
            for im, k in DcolsB(t).items():
                add(roff[0] + ridx[m][im], coff[0] + j, k)
            ku = (t[0] + 1, t[1] + 1, t[2], t[3], t[4])
            assert ku in ridx[m - 1], (w, ku)
            add(roff[1] + ridx[m - 1][ku], coff[0] + j, m)
    # middle blocks k = m-1 .. 1: unknowns C_k at coff[m-k], equations E_k, E_{k-1}
    for k in range(m - 1, 0, -1):
        ck = coff[m - k]  # column block for C_k
        ek = roff[m - k]  # equation block E_k
        ekm = roff[m - k + 1]  # equation block E_{k-1}
        for j, t in enumerate(B[k]):
            for im, kk in DcolsB(t).items():
                add(ek + ridx[k][im], ck + j, kk)
            ku = (t[0] + 1, t[1] + 1, t[2], t[3], t[4])
            assert ku in ridx[k - 1], (w, k, ku)
            add(ekm + ridx[k - 1][ku], ck + j, k)
    # bottom block C_0 at coff[m], equations E_0 (roff[m])
    ck = coff[m]
    ek = roff[m]
    for j, t in enumerate(B[0]):
        for im, kk in DcolsB(t).items():
            add(ek + ridx[0][im], ck + j, kk)
    return nrows, ncols, Dd, {"n": n, "s": s}

def sK_counts(wmax):
    # K-monomial counts, generator weights (1,1,6,4)
    dp = [0] * (wmax + 1)
    dp[0] = 1
    for g in (1, 1, 6, 4):
        for w in range(g, wmax + 1):
            dp[w] += dp[w - g]
    return dp

def bracket_pred(m, w, sk):
    seed = {4: 46, 5: 60, 6: 70}.get(m)
    if seed is None:
        return None
    a = sk[w - seed] if w - seed >= 0 else 0
    b = sk[w - seed - 2] if w - seed - 2 >= 0 else 0
    return a - b

emit("# tower_degm: m=%d J=(p^%d q^%d) [EXACT-QQ, Sage LinBox]" % (M, JP, JQ))
sk = sK_counts(max(weights) if weights else 0)

# self-test: chain-vs-direct at small weight
for w in (10, 14):
    if w > 8 * M:
        continue
    dom = Vmons_le(w, M)
    nn = len(dom)
    ridx = {m_: i for i, m_ in enumerate(dom)}
    Md = {}
    for j, m_ in enumerate(dom):
        for im, k in Dcols(m_).items():
            assert ridx.get(im) is not None
            Md[(ridx[im], j)] = Md.get((ridx[im], j), 0) + k
    assert (nn - matrix(QQ, nn, nn, Md, sparse=True).rank()) == (
        (lambda t: t[1] - matrix(QQ, t[0], t[1], t[2], sparse=True).rank())(
            build_chain_mats(w, M, JP, JQ, False)))
    emit("  self-test chain==direct at w=%d OK" % w)

for W in weights:
    emit("=== m=%d weight %d ===" % (M, W))
    t0 = time.time()
    dom = Vmons_le(W, M)
    nle = len(dom)
    ridx = {m_: i for i, m_ in enumerate(dom)}
    Md = {}
    for j, m_ in enumerate(dom):
        for im, k in Dcols(m_).items():
            i = ridx.get(im)
            assert i is not None, (W, im)
            Md[(i, j)] = Md.get((i, j), 0) + k
    r_res = matrix(QQ, nle, nle, Md, sparse=True).rank()
    N_le = nle - r_res
    t1 = time.time()
    nr, nc, Dd, meta = build_chain_mats(W, M, JP, JQ, True)
    assert nr == nle, (W, nr, nle)
    N_J = nc - matrix(QQ, nr, nc, Dd, sparse=True).rank()
    t2 = time.time()
    assert N_J <= N_le, (W, N_J, N_le)
    nviol = N_le - N_J
    pred = bracket_pred(M, W, sk)
    emit("n_le=%d N_J=%d nviol=%d pred=%s (res=%.1fs con=%.1fs)" % (
        N_le, N_J, nviol, pred, t1 - t0, t2 - t1))
    if pred is not None:
        if nviol == pred:
            emit("MATCH prediction (no new primitive at degree %d, w=%d)" % (M, W))
        elif nviol > pred:
            emit("EXCESS +%d at degree %d w=%d: ESCALATE (new primitive)" % (
                nviol - pred, M, W))
        else:
            emit("DEFICIT %d at degree %d w=%d (extra torsion)" % (
                pred - nviol, M, W))

with open(LOGPATH, "w") as fh:
    fh.write("\n".join(STS) + "\n")
