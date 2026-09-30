"""Certificate-route probe (exact QQ, SymPy).

Per weight w:
  (a) M·Rg = I - Kg·Gsel  solvable over QQ   [Gsel-projection route]
  (b) N = Gsel·B          solvable over QQ   [span(N) ⊆ span(Gsel)]
  (c) M·R  = I - K·N      solvable over QQ   [N-projection route]
  (d) diagnostics: rank_QQ vs CAS rank_Fp, null(M) vs null(M^T), rank(Eq).

Run: python3 scripts/cas/probe_routes.py [w_max]
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sympy import Matrix, Rational, symbols, Poly, expand
from check_s6 import Dmono, mono_w, s6, a0, a1, a2, a3, a4, a5, J1, J2, F0, HMONO
H = sum(Rational(c) * a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3] * a4**e[4] * a5**e[5]
        for c, e in HMONO)
GENS = [a4, a5, J1, J2, F0, H]

# CAS-verified (F_1000003) data: Kernel.lean / data/s6.log
CAS_N = {0: 1, 1: 2, 2: 4, 3: 7, 4: 11, 5: 17, 6: 25, 7: 35, 8: 49, 9: 66,
         10: 88, 11: 115, 12: 148, 13: 188, 14: 236, 15: 293, 16: 361,
         17: 440, 18: 533, 19: 640, 20: 764, 21: 906, 22: 1068, 23: 1252,
         24: 1461, 25: 1696, 26: 1961, 27: 2257, 28: 2588, 29: 2956,
         30: 3365, 31: 3817, 32: 4317, 33: 4867, 34: 5472, 35: 6135,
         36: 6861, 37: 7653, 38: 8517, 39: 9456, 40: 10477}
CAS_RANK = {0: 0, 1: 0, 2: 1, 3: 3, 4: 5, 5: 9, 6: 14, 7: 21, 8: 31,
            9: 44, 10: 61, 11: 83, 12: 109, 13: 142, 14: 181, 15: 229,
            16: 286, 17: 354, 18: 433, 19: 526, 20: 633, 21: 758,
            22: 900, 23: 1064, 24: 1248, 25: 1458, 26: 1694, 27: 1961,
            28: 2258, 29: 2592, 30: 2961, 31: 3373, 32: 3827, 33: 4331,
            34: 4884, 35: 5495, 36: 6161, 37: 6893, 38: 7689, 39: 8560,
            40: 9505}

a0, a1, a2, a3, a4, a5 = symbols("a0 a1 a2 a3 a4 a5")
J1 = 2 * a1 * a4 - a2**2
J2 = 2 * a2 * a5 - a3**2
F0 = (a4**2 * a5**4 * a0 - a4 * a5**3 * a3 * a2 * a1
      + Rational(1, 3) * a4 * a5**2 * a3**3 * a1
      + Rational(1, 3) * a5**2 * a3**3 * a2**2
      - Rational(1, 5) * a5 * a3**5 * a2 + Rational(1, 35) * a3**7)
HMONO = [((11025), [2, 0, 0, 0, 4, 4]), ((-22050), [1, 1, 1, 1, 3, 3]),
         ((7350), [1, 1, 0, 3, 3, 2]), ((7350), [1, 0, 2, 3, 2, 2]),
         ((-4410), [1, 0, 1, 5, 2, 1]), ((630), [1, 0, 0, 7, 2, 0]),
         ((11025), [0, 2, 2, 2, 2, 2]), ((-7350), [0, 2, 1, 4, 2, 1]),
         ((1225), [0, 2, 0, 6, 2, 0]), ((6720), [0, 1, 5, 0, 1, 3]),
         ((-16800), [0, 1, 4, 2, 1, 2]), ((9450), [0, 1, 3, 4, 1, 1]),
         ((-1540), [0, 1, 2, 6, 1, 0]), ((-2208), [0, 0, 7, 0, 0, 3]),
         ((4368), [0, 0, 6, 2, 0, 2]), ((-2352), [0, 0, 5, 4, 0, 1]),
         ((385), [0, 0, 4, 6, 0, 0])]
H = sum(Rational(c) * a0**e[0] * a1**e[1] * a2**e[2] * a3**e[3] * a4**e[4]
        * a5**e[5] for c, e in HMONO)
GENS = [a4, a5, J1, J2, F0, H]


def dmat_int(w):
    dom = mono_w(w)
    ridx = {m: i for i, m in enumerate(dom)}
    n = len(dom)
    M = [[0] * n for _ in range(n)]
    for j, mm in enumerate(dom):
        for nm, k in Dmono(mm).items():
            assert nm in ridx, "weight drift at w=%d" % w
            M[ridx[nm]][j] += k
    return dom, M


def gen_mono_exps(w):
    """(ep,eq,ej1,ej2,ef,eh) with GEN_WTS-weight w, producer loop order."""
    out = []
    for eh in range(w // 24 + 1):
        for ef in range((w - 24 * eh) // 14 + 1):
            for ej2 in range((w - 24 * eh - 14 * ef) // 4 + 1):
                for ej1 in range((w - 24 * eh - 14 * ef - 4 * ej2) // 6 + 1):
                    for ep in range(w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 + 1):
                        rest = w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 - ep
                        out.append((ep, rest, ej1, ej2, ef, eh))
    return out


def eval_col(w, ridx, exps):
    """Rational coordinate vector of the generator monomial with `exps`."""
    f = Rational(1)
    for g, e in zip(GENS, exps):
        f *= g ** e
    d = Poly(expand(f), a0, a1, a2, a3, a4, a5).as_dict()
    col = [Rational(0)] * len(ridx)
    for (i0, i1, i2, i3, i4, i5), c in d.items():
        key = (i0, i1, i2, i3, i4, i5)
        if key in ridx:
            col[ridx[key]] += c
    return col


def solve(M, rhs_cols):
    """Is M·X = rhs_cols solvable over QQ? (exact QQ RREF consistency)"""
    n, m = M.shape
    t = len(rhs_cols)
    if t == 0:
        return True
    B = Matrix(n, t, [col[i] for col in rhs_cols for i in range(n)])
    A = M.row_join(B)
    A_rref, pivs = A.rref()
    for r in range(len(pivs), n):
        if A_rref[r, m] != 0:
            return False
    return True


def probe(w):
    t0 = time.time()
    dom, Mint = dmat_int(w)
    n = len(dom)
    ridx = {m: i for i, m in enumerate(dom)}
    MQ = Matrix(Mint)
    R, pivs = MQ.rref()
    r = len(pivs)
    k = n - r
    pred = s6(w) - (s6(w - 28) if w >= 28 else 0)
    free = [j for j in range(n) if j not in pivs]
    Ncols = []
    for f in free:
        v = [Rational(0)] * n
        v[f] = Rational(1)
        for i, p in enumerate(pivs):
            v[p] = -R[i, f]
        Ncols.append(v)
    N = Matrix.hstack(*[Matrix(v) for v in Ncols]) if Ncols else Matrix(n, 0)
    Ecols = [eval_col(w, ridx, e) for e in gen_mono_exps(w)]
    Eq = Matrix(Ecols).T if Ecols else Matrix(n, 0)
    rankE = Eq.rank() if Ecols else 0
    piveq = Eq.rref()[1] if Ecols else ()
    selIdx = sorted(piveq)
    Gsel = Matrix.hstack(*[Eq[:, j] for j in selIdx]) if selIdx else Matrix(n, 0)
    okG = (len(selIdx) == k)
    route_a = route_b = route_c = duality = True
    if k > 0:
        Kg = (Gsel.T * Gsel).inv() * Gsel.T
        Pg = Gsel * Kg
        assert Pg * Gsel == Gsel, "Gsel columns not fixed by projection"
        Sg = [(Matrix.eye(n) - Pg)[:, j] for j in range(n)]
        route_a = solve(MQ, Sg)
        K = (N.T * N).inv() * N.T
        Pn = N * K
        assert Pn * N == N, "N columns not fixed by projection"
        Sn = [(Matrix.eye(n) - Pn)[:, j] for j in range(n)]
        route_c = solve(MQ, Sn)
        route_b = solve(Gsel, Ncols)
        duality = (len(MQ.T.nullspace()) == k)
    dt = time.time() - t0
    line = (f"w={w:2d} n={n:5d} r={r:4d} k={k:4d} pred={pred:4d} "
            f"nFp={CAS_N.get(w, '?')} rFp={CAS_RANK.get(w, '?')} "
            f"s6={s6(w):5d} rankEq={rankE:4d} sel==k:{okG!s:5} "
            f"a:{route_a!s:5} b:{route_b!s:5} c:{route_c!s:5} "
            f"dual:{duality!s:5} {dt:7.1f}s")
    print(line, flush=True)
    ok = (r == CAS_RANK.get(w) and n == CAS_N.get(w) and k == pred and okG)
    return ok, line


def main():
    wmax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    allok = True
    for w in range(0, wmax + 1):
        ok, _ = probe(w)
        allok &= ok
    print("probe_routes " + ("OK" if allok else "FAILED"))
    return 0 if allok else 1


if __name__ == "__main__":
    raise SystemExit(main())