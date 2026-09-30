"""Degree-3 top census vs J_3 = (p^6 q^8) over exact QQ (Sage).

For each weight w, two exact sparse-QQ rank verdicts (LinBox):
  N_le3(w) = nullity of D5 on V_w^{a0<=3}   (direct restricted matrix)
  N_J(w)   = nullity of the J_3-constrained chain
             (top C_3 parametrized as p^6 q^8 * u, u in B_{w-38})
Violation <=> N_J < N_le3 (some kernel vector has a0-degree-3 top
outside J_3).  No-violation (N_J == N_le3) is evidence, NOT proof,
beyond the weights checked.
Also records N_le2 / dimT = N_le3 - N_le2 (how many degree-3 tops exist).

Blocked construction reuses the Vmons/Dcols pattern of exact_ranks.sage:
domain V_w^{a0<=3} = a0^0*B_w (+) a0^1*B_{w-8} (+) a0^2*B_{w-16}
(+) a0^3*B_{w-24} (chain tops).  The chain form D(F)=0 <->
  D(C3)=0; D(C2)+3*a1a2*C3=0; D(C1)+2*a1a2*C2=0; D(C0)+a1a2*C1=0
(Ck in B) is validated against the direct matrix in the self-test.
No solve_right call is used anywhere.  The verdict is the blocked
exact-rank comparison N_J vs N_le3; the violation branch (runs only
if N_J < N_le3) extracts witnesses via an explicit right_kernel basis
plus a per-vector exact remainder check `ttop % div` (nonzero
certifies a top outside J_3).

Run: sage scripts/sage/tower_deg3.sage [w1 w2 ...] [log=PATH] [append=1]
Default weights (pilot): 38..48.  Extension: pass 49..60 explicitly.
Writes: data/tower_deg3.log (overwrite unless append=1)
"""

import sys
import time
import os

STS = []
def emit(s):
    print(s, flush=True)
    STS.append(s)

# ---------------------------------------------------------------- 6-tuple side (direct restricted matrix, exact_ranks pattern)
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
    # D(a_i) = a_{i+1} a_{i+2} for i <= 3, else 0.
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

# ---------------------------------------------------------------- 5-tuple (B = k[a1..a5]) side, chain blocks
def Bmons5(d):
    # 5-tuples (e1..e5), weights (5,3,2,1,1), total d; [] if d < 0.
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
    # D on B-monomials (5-tuples): only a1,a2,a3 move.
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

def in_J3(t5):
    # Exact divisibility of a B-monomial by p^6 q^8 (== remainder zero
    # upon division in the polynomial ring; divisor is a monomial).
    return t5[3] >= 6 and t5[4] >= 8

def build_chain_mats(w, constrained):
    """Block matrices for the a0-chain at weight w.

    constrained=False: unknowns (C3,C2,C1,C0), cols n3+n2+n1+n0.
    constrained=True:  unknowns (u,C2,C1,C0) with C3 = p^6q^8*u,
                       cols s+n2+n1+n0.
    Returns (nrows, ncols, dict, meta). Rows: E3(n3) E2(n2) E1(n1) E0(n0).
    """
    B = [Bmons5(w - 8 * k) for k in range(4)]  # B0..B3 as 5-tuples
    n = [len(B[k]) for k in range(4)]
    ridx = [{t: i for i, t in enumerate(B[k])} for k in range(4)]
    U = Bmons5(w - 38) if constrained else B[3]
    s = len(U)
    # column offsets: [top-block | C2 | C1 | C0]
    coff = [0, s, s + n[2], s + n[2] + n[1]]
    ncols = s + n[2] + n[1] + n[0]
    # row offsets: [E3 | E2 | E1 | E0]
    roff = [0, n[3], n[3] + n[2], n[3] + n[2] + n[1]]
    nrows = n[3] + n[2] + n[1] + n[0]
    Dd = {}
    def add(r, c, v):
        if v:
            Dd[(r, c)] = Dd.get((r, c), 0) + v
    if constrained:
        for j, u in enumerate(U):
            e1, e2, e3, e4, e5 = u
            # E3 row: D(p^6 q^8 u)
            mu = (e1, e2, e3, e4 + 6, e5 + 8)
            for im, k in DcolsB(mu).items():
                add(roff[0] + ridx[3][im], coff[0] + j, k)
            # E2 row: 3 a1a2 p^6 q^8 u
            ku = (e1 + 1, e2 + 1, e3, e4 + 6, e5 + 8)
            add(roff[1] + ridx[2][ku], coff[0] + j, 3)
    else:
        for j, t in enumerate(U):  # U == B3 here
            for im, k in DcolsB(t).items():
                add(roff[0] + ridx[3][im], coff[0] + j, k)
            ku = (t[0] + 1, t[1] + 1, t[2], t[3], t[4])
            add(roff[1] + ridx[2][ku], coff[0] + j, 3)
    for j, t in enumerate(B[2]):
        for im, k in DcolsB(t).items():
            add(roff[1] + ridx[2][im], coff[1] + j, k)
        ku = (t[0] + 1, t[1] + 1, t[2], t[3], t[4])
        add(roff[2] + ridx[1][ku], coff[1] + j, 2)
    for j, t in enumerate(B[1]):
        for im, k in DcolsB(t).items():
            add(roff[2] + ridx[1][im], coff[2] + j, k)
        ku = (t[0] + 1, t[1] + 1, t[2], t[3], t[4])
        add(roff[3] + ridx[0][ku], coff[2] + j, 1)
    for j, t in enumerate(B[0]):
        for im, k in DcolsB(t).items():
            add(roff[3] + ridx[0][im], coff[3] + j, k)
    meta = {"n": n, "s": s}
    return nrows, ncols, Dd, meta

# ---------------------------------------------------------------- self-test (tiny weights, instant)
def self_test():
    # (a) J_3 divisibility on monomials: generators c^3, c*h2 in; low exponents out.
    assert in_J3((0, 0, 0, 6, 12))      # c^3 = p^6 q^12
    assert in_J3((0, 0, 0, 6, 8))       # c*h2 = 11025 p^6 q^8
    assert not in_J3((0, 0, 0, 5, 8))
    assert not in_J3((0, 0, 0, 6, 7))
    assert not in_J3((0, 0, 0, 0, 0))
    # (b) chain-vs-direct agreement: null(chain_uncon) == null(direct) at w=10,14.
    for w in (10, 14):
        dom = Vmons_le(w, 3)
        nn = len(dom)
        ridx = {m: i for i, m in enumerate(dom)}
        Md = {}
        for j, m in enumerate(dom):
            for im, k in Dcols(m).items():
                i = ridx.get(im)
                assert i is not None, "D leaves V^{<=3} at w=%d" % w
                Md[(i, j)] = Md.get((i, j), 0) + k
        Mres = matrix(QQ, nn, nn, Md, sparse=True)
        nr, nc, Dd, meta = build_chain_mats(w, False)
        assert nr == nn, (w, nr, nn)
        assert nc == nn, (w, nc, nn)
        Mc = matrix(QQ, nr, nc, Dd, sparse=True)
        assert (nn - Mres.rank()) == (nc - Mc.rank()), "chain/direct mismatch at %d" % w
    # (c) constrained builder nonempty for pilot floor w=38.
    nr, nc, Dd, meta = build_chain_mats(38, True)
    assert meta["s"] == 1 and nr > 0 and nc > 0
    # (d) constrained-equivalence: N_J equals an INDEPENDENT per-vector
    #     J_3-compatibility count at w=10,14 (direct nullspace feasible).
    #     Independent path uses only the direct matrix + polynomial
    #     remainder (never the constrained-chain builder): the compatible
    #     subspace {v in ker : top(v) % p^6q^8 == 0} has dimension
    #     dimK - rank(A), where A is the outside-top coefficient matrix
    #     (rows = a0^3 monomials failing in_J3, cols = kernel basis).
    #     A naive "count basis vectors with divisible tops" would be
    #     basis-dependent; the rank formula is the basis-independent
    #     dimension.  At w=10,14 there are no a0^3 monomials at all, so
    #     O is empty and the count is trivially dimK -- the test still
    #     exercises the full pipeline (kernel basis -> top extraction ->
    #     remainder-zero check -> rank) and pins N_J == indep == N_le3
    #     plus the unconstrained-chain count N_U == N_le3 (calibration).
    #     Any failure STOPS here (BLOCKED) -- do not force it.
    R = PolynomialRing(QQ, "a0,a1,a2,a3,a4,a5")
    g = R.gens()
    div = g[4]**6 * g[5]**8
    for w in (10, 14):
        dom = Vmons_le(w, 3)
        nn = len(dom)
        ridx = {m: i for i, m in enumerate(dom)}
        Md = {}
        for j, m in enumerate(dom):
            for im, k in Dcols(m).items():
                Md[(ridx[im], j)] = Md.get((ridx[im], j), 0) + k
        Mres = matrix(QQ, nn, nn, Md, sparse=True)
        N_le3 = nn - Mres.rank()
        nrJ, ncJ, DdJ, metaJ = build_chain_mats(w, True)
        N_J = ncJ - matrix(QQ, nrJ, ncJ, DdJ, sparse=True).rank()
        nrU, ncU, DdU, metaU = build_chain_mats(w, False)
        N_U = ncU - matrix(QQ, nrU, ncU, DdU, sparse=True).rank()
        assert N_U == N_le3, (w, N_U, N_le3)
        K = Mres.right_kernel()
        basis = K.basis()
        assert len(basis) == N_le3, (w, len(basis), N_le3)
        didx = {m: j for j, m in enumerate(dom)}
        O = [m for m in dom if m[0] == 3 and not in_J3(m[1:])]
        for v in basis:
            assert Mres * v == 0
            top_terms = [(dom[j], v[j]) for j in range(nn) if v[j] != 0 and dom[j][0] == 3]
            mono_ok = all(m[4] >= 6 and m[5] >= 8 for m, _ in top_terms)
            ttop = sum((c * prod(g[i]**e for i, e in enumerate(m)) for m, c in top_terms), R.zero())
            rem_ok = (ttop % div == 0)
            assert mono_ok == rem_ok, (w, mono_ok, rem_ok)
        if O:
            Ad = {}
            for k, v in enumerate(basis):
                for i, m in enumerate(O):
                    c = v[didx[m]]
                    if c != 0:
                        Ad[(i, k)] = c
            rankA = matrix(QQ, len(O), len(basis), Ad, sparse=True).rank()
        else:
            rankA = 0
        indep = len(basis) - rankA
        assert indep == N_J, (w, indep, N_J, N_le3, N_U)
        emit("  equiv w=%d: N_J=%d indep=%d N_le3=%d N_U=%d rankA=%d" % (w, N_J, indep, N_le3, N_U, rankA))
    emit("self-test OK (J3 divisibility, chain==direct at 10/14, equiv N_J==indep at 10/14, w38 constrained nonempty)")

# ---------------------------------------------------------------- argv
weights = []
LOGPATH = "data/tower_deg3.log"
APPEND = False
for x in sys.argv[1:]:
    if x.startswith("log="):
        LOGPATH = x[4:]
    elif x == "append=1":
        APPEND = True
    else:
        weights.append(int(x))
if not weights:
    weights = list(range(38, 49))  # pilot default

old = ""
if APPEND and os.path.exists(LOGPATH):
    with open(LOGPATH) as fh:
        old = fh.read()
    emit("# tower_deg3 (append): existing log kept (%d chars)" % len(old))
else:
    emit("# tower_deg3: degree-3 top census vs J_3=(p^6q^8) [EXACT-QQ, Sage LinBox]")
    emit("# method: N_le3 = null(D|V^{a0<=3}); N_J = null(J3-constrained chain); viol <=> N_J < N_le3")

self_test()

viol_any = False
for W in weights:
    emit("=== weight %d ===" % W)
    t0 = time.time()
    dom = Vmons_le(W, 3)
    nle3 = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    Md = {}
    for j, m in enumerate(dom):
        for im, k in Dcols(m).items():
            i = ridx.get(im)
            assert i is not None, "D leaves V^{<=3} at w=%d" % W
            Md[(i, j)] = Md.get((i, j), 0) + k
    Mres = matrix(QQ, nle3, nle3, Md, sparse=True)
    t1 = time.time()
    r_res = Mres.rank()
    N_le3 = nle3 - r_res
    t2 = time.time()
    # N_le2 (degree<=2 restriction) for dimT context
    dom2 = Vmons_le(W, 2)
    nle2 = len(dom2)
    ridx2 = {m: i for i, m in enumerate(dom2)}
    Md2 = {}
    for j, m in enumerate(dom2):
        for im, k in Dcols(m).items():
            Md2[(ridx2[im], j)] = Md2.get((ridx2[im], j), 0) + k
    Mle2 = matrix(QQ, nle2, nle2, Md2, sparse=True)
    r_le2 = Mle2.rank()
    N_le2 = nle2 - r_le2
    dimT = N_le3 - N_le2
    t3 = time.time()
    # J3-constrained chain
    nr, nc, Dd, meta = build_chain_mats(W, True)
    assert nr == nle3, (W, nr, nle3)
    n0, n1, n2, n3 = meta["n"][0], meta["n"][1], meta["n"][2], meta["n"][3]
    Mc = matrix(QQ, nr, nc, Dd, sparse=True)
    r_con = Mc.rank()
    N_J = nc - r_con
    t4 = time.time()
    assert N_J <= N_le3, (W, N_J, N_le3)
    viol = (N_J < N_le3)
    viol_any = viol_any or viol
    emit("blocks: Bw=%d Bw-8=%d Bw-16=%d Bw-24=%d n_le3=%d s=Bw-38=%d" % (n0, n1, n2, n3, nle3, meta["s"]))
    emit("N_le3=%d N_le2=%d dimT=%d N_J=%d violation=%s nviol=%d" % (
        N_le3, N_le2, dimT, N_J, "YES" if viol else "no", N_le3 - N_J))
    emit("times: res=%.1fs le2=%.1fs con=%.1fs" % (t2 - t1, t3 - t2, t4 - t3))
    if viol:
        emit("VIOLATION at w=%d: extracting witness (right_kernel basis + per-vector remainder check; no solve_right)" % W)
        # Explicit kernel basis, then exact top-divisibility per vector.
        K = Mres.right_kernel()
        R = PolynomialRing(QQ, "a0,a1,a2,a3,a4,a5")
        g = R.gens()
        p, q = g[4], g[5]
        div = p**6 * q**8
        found = 0
        for v in K.basis():
            assert Mres * v == 0
            top_terms = [(dom[j], v[j]) for j in range(nle3) if v[j] != 0 and dom[j][0] == 3]
            if not top_terms:
                continue
            ok = all(m[4] >= 6 and m[5] >= 8 for m, _ in top_terms)
            if not ok:
                found += 1
                ttop = sum(c * prod(g[i]**e for i, e in enumerate(m)) for m, c in top_terms)
                rem = ttop % div  # exact remainder; nonzero certifies outside J_3
                assert rem != 0
                emit("  witness vec: nnz=%d top_nnz=%d rem_nnz=%d" % (
                    sum(1 for j in range(nle3) if v[j] != 0), len(top_terms),
                    len(rem.dict()) if rem != 0 else 0))
        emit("  violating directions with deg-3 top outside J_3: %d (ESCALATE: new primitive)" % found)

emit("# summary weights %s: %s" % (
    weights, "VIOLATION FOUND (see above)" if viol_any else "no degree-3 violation (evidence, not proof)"))

with open(LOGPATH, "w") as fh:
    fh.write(old + "\n".join(STS) + "\n")
