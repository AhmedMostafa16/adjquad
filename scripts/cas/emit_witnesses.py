"""Emit Lean-checkable rank/nullity witnesses for D|V_w (exact QQ, SymPy).

M matches check_s6.nullity over ZZ (Dmono coefficients). genMonos order
(p,q,J1,J2,F0,H weights 1,1,6,4,14,24; nested eH,eF,eJ2,eJ1,ep loops,
eq = rest) matches WeightData.genMonos.

Run: python3 scripts/cas/emit_witnesses.py --weights 0,1,4,6 [--with-M]

Selected columns are scaled by D0 = LCM of coefficient denominators,
so all emitted entries are integral; Lean checks
Gsel[i][j]*c.den = D0*c.num.
"""

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import Matrix, Rational

from check_s6 import Dmono, mono_w, s6

GEN_WTS = [1, 1, 6, 4, 14, 24]


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


def _to_int(mat):
    denoms = [Rational(x).q for x in mat]
    L = 1
    for d in denoms:
        a, b = L, d
        while b:
            a, b = b, a % b
        L = L * d // a
    return [[int(Rational(x) * L) for x in row] for row in mat.tolist()], L


def _gen_mono_exps(w):
    """Exponent tuples (ep,eq,ej1,ej2,ef,eh) of total GEN_WTS-weight w."""
    out = []
    for eh in range(w // 24 + 1):
        for ef in range((w - 24 * eh) // 14 + 1):
            for ej2 in range((w - 24 * eh - 14 * ef) // 4 + 1):
                for ej1 in range((w - 24 * eh - 14 * ef - 4 * ej2) // 6 + 1):
                    for ep in range(w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 + 1):
                        rest = w - 24 * eh - 14 * ef - 4 * ej2 - 6 * ej1 - ep
                        out.append((ep, rest, ej1, ej2, ef, eh))
    return out


def _zeros(n, m):
    return [[0] * m for _ in range(n)]


def witness_for_weight(w):
    dom, M = dmat_int(w)
    n = len(dom)
    Mq = Matrix(M)
    pivs = Mq.T.rref()[1]
    S = sorted(pivs)
    r = len(S)
    A = Mq.extract(S, list(range(n)))
    if r == 0:
        # Degenerate rank-0 case (w=0,1: M is the zero matrix). The
        # pseudoinverse equations are vacuous; T/C are n×0 zero-column
        # matrices realized as n empty rows.
        T, d1 = _zeros(n, 0), 1
        C, d4 = _zeros(n, 0), 1
    else:
        G = (A * A.T).inv()
        Tq = A.T * G
        Cq = (G * A * Mq.T).T
        T, d1 = _to_int(Tq)
        C, d4 = _to_int(Cq)
    Ns = Mq.nullspace()
    k = len(Ns)
    assert r + k == n, "rank-nullity fail at w=%d" % w
    if k == 0:
        N, K, d3 = _zeros(n, 0), _zeros(0, n), 1
    else:
        Nq = Matrix.hstack(*Ns)
        H = (Nq.T * Nq).inv()
        Kq = H * Nq.T
        # _to_int scales N by LN; fold into d3 so K·N = d3·I with d3 = L3*LN.
        N, LN = _to_int(Nq)
        K, d3 = _to_int(Kq)
        d3 = d3 * LN
    # Generator side: Gsel columns are D0 * col with D0 = LCM of
    # coefficient denominators at w; Kg on the exact matrix gives
    # Kg * Gsel = dg * I with dg = LK * D0.
    from check_s6 import F0, H, J1, J2, a0, a1, a2, a3, a4, a5
    from sympy import Poly, expand
    gens = [a4, a5, J1, J2, F0, H]
    sel = _gen_mono_exps(w)
    ridx = {m: i for i, m in enumerate(dom)}
    Ecols = []
    denoms = [1]
    for exps in sel:
        f = 1
        for g, e in zip(gens, exps):
            f *= g ** e
        d = Poly(expand(f), a0, a1, a2, a3, a4, a5).as_dict()
        col = [Rational(0)] * n
        for (i0, i1, i2, i3, i4, i5), c in d.items():
            col[ridx[(i0, i1, i2, i3, i4, i5)]] += Rational(c)
        denoms.extend(x.q for x in col)
        Ecols.append(col)
    D0 = 1
    for dd in denoms:
        a, b = D0, dd
        while b:
            a, b = b, a % b
        D0 = D0 * dd // a
    Eq = Matrix(Ecols).T if Ecols else Matrix.zeros(n, 0)
    pivc = Eq.rref()[1] if Ecols else ()
    selIdx = sorted(pivc)
    assert len(selIdx) == k, "subalgebra shortfall at w=%d" % w
    Esel = Eq.extract(list(range(n)), selIdx)
    # CAS certificate for the kernel-spanning premise (hker direction 1):
    # every selected genMono vector lies in the integer kernel.
    for j in selIdx:
        assert Mq * Matrix(Ecols[j]) == Matrix.zeros(n, 1), \
            "genMono %d not in kernel at w=%d" % (j, w)
    Hg = (Esel.T * Esel).inv()
    Kgq = Hg * Esel.T
    Gsel = [[int(Rational(x) * D0) for x in row] for row in Esel.tolist()]
    Kg, LK = _to_int(Kgq)
    dg = LK * D0
    # hker left-inverse certificates (kernel-spanning; see Lean hker_14):
    #   L C = dL I_r  (left inverse of C; C has rank r = rank M)
    #   Y (A; Kg) = dY I_n  (left inverse of Q = M[S] vstack Kg, n x n)
    # Exact rational elimination; identities re-verified below, by the
    # oracle, and by native_decide in Lean.
    Cq = Matrix(C)
    if r == 0:
        L, dL = _zeros(0, n), 1
    else:
        assert Cq.rank() == r, "C rank shortfall at w=%d" % w
        Lq = (Cq.T * Cq).inv() * Cq.T
        L, dL = _to_int(Lq)
        assert dL != 0
    A_int = [[int(x) for x in row] for row in A.tolist()]
    Q = A_int + Kg
    Qq = Matrix(Q)
    assert Qq.rank() == n, "Q = [A; Kg] singular at w=%d" % w
    Y, dY = _to_int(Qq.inv())
    assert dY != 0
    for i in range(r):
        for j in range(r):
            s = sum(L[i][t] * C[t][j] for t in range(n))
            assert s == (dL if i == j else 0), "L C != dL I at w=%d" % w
    for i in range(n):
        for j in range(n):
            s = sum(Y[i][t] * Q[t][j] for t in range(n))
            assert s == (dY if i == j else 0), "Y Q != dY I at w=%d" % w
    # Auxiliary certificates retained for compatibility with the checker:
    #   Gsel X = dX N  (N is a scaled combination of selected columns)
    #   M^T B = dB (d3 I - N K).
    # The latter orientation does NOT allow cancelling from M v = 0:
    # M^T B v need not vanish. Kernel spanning uses Y (A; Kg) = dY I,
    # together with M Gsel = 0 and Kg Gsel = dg I, instead.
    Nq = Matrix(N)
    Gselq = Matrix(Gsel)
    Xq = (Gselq.T * Gselq).inv() * Gselq.T * Nq
    assert Gselq * Xq == Nq, "Gsel X != N at w=%d" % w
    X, dX = _to_int(Xq)
    assert dX != 0
    # Factor through M^T because im(d3 I - N K) = row(M); factoring
    # through M instead is not valid in general since col(M) != row(M).
    # This is only an auxiliary matrix identity, not the spanning proof.
    # Exact CAS verifies the orientation below; Lean and the oracle check
    # M^T B = dB (d3 I - N K) independently.
    A0 = d3 * Matrix.eye(n) - Matrix(N) * Matrix(K)
    if r == 0:
        # M = 0: A0 = 0 (N, K square with K N = d3 I); take B = 0.
        assert A0 == Matrix.zeros(n, n), "A0 != 0 at rank-0 w=%d" % w
        B, dB = _zeros(n, n), 1
        assert Mq * Matrix(B).T == A0
    else:
        # Construct a candidate through the selected-row factorization.
        # Cq here is the emitted integer C (M = Cq A / d4); check the
        # resulting identity exactly rather than assuming cancellation.
        Bq = Cq * (Cq.T * Cq).inv() * G * A * A0
        assert Mq.T * Bq == A0, "M^T B != d3 I - N K at w=%d" % w
        B, dB = _to_int(Bq)
        assert dB != 0
    return {"w": w, "n": n, "r": r, "k": k, "M": M, "S": S,
             "T": T, "C": C, "N": N, "K": K, "d1": d1, "d4": d4, "d3": d3,
             "Gsel": Gsel, "Kg": Kg, "dg": dg, "selIdx": selIdx,
             "D0": D0, "Ecols": Ecols, "L": L, "dL": dL, "Y": Y, "dY": dY,
             "X": X, "dX": dX, "B": B, "dB": dB}


def _lean_mat(m):
    return "[" + ", ".join("[" + ", ".join(str(x) for x in row) + "]" for row in m) + "]"


def _lean_natlist(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


# Max chars per emitted matrix-literal def. Larger matrices are split into
# row-blocks (each a complete def) joined by `++`, so no single command
# overwhelms elaboration (mvar synthesis on giant literals). The joined
# value is identical; theorems reference the joiner name.
_SPLIT_AT = 20000


def _emit_mat(w, name, mat):
    full = _lean_mat(mat)
    if len(full) <= _SPLIT_AT or not mat:
        return ["def W%d%s : IMat := %s" % (w, name, full)], "W%d%s" % (w, name)
    # Greedily chunk rows to stay under the threshold.
    chunks, cur, cur_len = [], [], 0
    for row in mat:
        rs = "[" + ", ".join(str(x) for x in row) + "]"
        if cur and cur_len + len(rs) + 2 > _SPLIT_AT:
            chunks.append(cur)
            cur, cur_len = [], 0
        cur.append(rs)
        cur_len += len(rs) + 2
    if cur:
        chunks.append(cur)
    lines = []
    for i, ch in enumerate(chunks):
        lines.append("def W%d%s_b%d : IMat := [%s]" % (w, name, i, ", ".join(ch)))
    joiner = " ++ ".join("W%d%s_b%d" % (w, name, i) for i in range(len(chunks)))
    lines.append("def W%d%s : IMat := %s" % (w, name, joiner))
    return lines, "W%d%s" % (w, name)

def render_lean(wit, with_M):
    w = wit["w"]
    L = []
    L.append("def W%dS : List Nat := %s" % (w, _lean_natlist(wit["S"])))
    refs = {}
    for name in ("T", "C", "N", "K", "Gsel", "Kg", "L", "Y", "X", "B"):
        lines, ref = _emit_mat(w, name, wit[name])
        L.extend(lines)
        refs[name] = ref
    for name in ("d1", "d4", "d3", "dg"):
        L.append("def W%d%s : Int := %d" % (w, name, wit[name]))
    L.append("def W%dD0 : Int := %d" % (w, wit["D0"]))
    L.append("def W%dselIdx : List Nat := %s" % (w, _lean_natlist(wit["selIdx"])))
    if with_M:
        mlines, mref = _emit_mat(w, "M", wit["M"])
        L.extend(mlines)
        L.append("theorem mats_match_%d : dmat %d = %s := by native_decide"
                 % (w, w, mref))
    L.append("theorem witness_ok_%d : checkWitness (dmat %d) W%dS %s %s %s %s %s %s "
             "W%dd1 W%dd4 W%dd3 W%ddg %d %d := by native_decide"
             % (w, w, w, refs["T"], refs["C"], refs["N"], refs["K"],
                refs["Gsel"], refs["Kg"], w, w, w, w, wit["r"], wit["k"]))
    L.append("theorem gselKernel_%d : imatMul (dmat %d) %s = imatZero %d %d "
             ":= by native_decide" % (w, w, refs["Gsel"], wit["n"], wit["k"]))
    L.append("theorem gselDecode_%d : gselDecode %d W%dselIdx %s W%dD0 = true "
             ":= by native_decide" % (w, w, w, refs["Gsel"], w))
    L.append("def W%dA : IMat := imatRowsOf (dmat %d) W%dS" % (w, w, w))
    L.append("def W%dQ : IMat := W%dA ++ W%dKg" % (w, w, w))
    L.append("def W%ddL : Int := %d" % (w, wit["dL"]))
    L.append("def W%ddY : Int := %d" % (w, wit["dY"]))
    L.append("def W%ddB : Int := %d" % (w, wit["dB"]))
    L.append("def W%ddX : Int := %d" % (w, wit["dX"]))
    L.append("theorem leftInv_%d : imatMul W%dL W%dC = imatSmul W%ddL (imatEye %d) "
             ":= by native_decide" % (w, w, w, w, wit["r"]))
    L.append("theorem qLeftInv_%d : imatMul W%dY W%dQ = imatSmul W%ddY (imatEye %d) "
             ":= by native_decide" % (w, w, w, w, wit["n"]))
    L.append("theorem leftInv_nz_%d : W%ddL ≠ 0 := by decide" % (w, w))
    L.append("theorem qLeftInv_nz_%d : W%ddY ≠ 0 := by decide" % (w, w))
    L.append("theorem shape_ok_%d : imatRows %s = %d ∧ imatCols %s = %d ∧ "
             "imatRows %s = %d ∧ imatCols %s = %d ∧ imatCols W%dQ = %d ∧ "
             "imatCols %s = imatRows W%dQ ∧ (∀ i ∈ W%dS, i < %d) "
             ":= by native_decide"
             % (w, refs["Gsel"], wit["n"], refs["Gsel"], wit["k"],
                refs["Kg"], wit["k"], refs["Kg"], wit["n"], w, wit["n"],
                refs["Y"], w, w, wit["n"]))
    L.append("theorem kerFactor_%d : imatMul (imatTranspose (dmat %d)) W%dB = "
             "imatSmul W%ddB (imatSub (imatSmul W%dd3 (imatEye %d)) (imatMul W%dN W%dK)) "
             ":= by native_decide" % (w, w, w, w, w, wit["n"], w, w))
    L.append("theorem xGsel_%d : imatMul %s W%dX = imatSmul W%ddX %s "
             ":= by native_decide" % (w, refs["Gsel"], w, w, refs["N"]))
    L.append("theorem xGsel_nz_%d : W%ddX ≠ 0 := by decide" % (w, w))
    L.append("theorem kerFactor_nz_%d : W%ddB ≠ 0 := by decide" % (w, w))
    return "\n".join(L)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--weights", default="0,1,4,6")
    ap.add_argument("--with-M", dest="with_M", action="store_true")
    ap.add_argument("--lean-out", default=None)
    ap.add_argument("--json-out", default=None)
    args = ap.parse_args(argv)
    weights = [int(x) for x in args.weights.split(",") if x.strip() != ""]
    wits = [witness_for_weight(w) for w in weights]
    if args.json_out:
        with open(args.json_out, "w") as f:
            json.dump(wits, f, default=lambda x: float(x))
    if args.lean_out:
        parts = ["-- GENERATED (UNTRUSTED input for Lean checking). Do not edit.",
                 "-- Produced by scripts/cas/emit_witnesses.py; verified in Lean",
                 "-- by mats_match_*/witness_ok_*/gselKernel_*/gselDecode_*/leftInv_*/qLeftInv_*",
                 "import AdjQuad.Generation",
                 "-- Compute budgets raised for large-n kernel evaluation",
                 "-- (soundness-neutral: only timeout/recursion guards).",
                 "set_option maxHeartbeats 1000000",
                 "set_option maxRecDepth 100000"]
        for wit in wits:
            parts.append(render_lean(wit, args.with_M))
        with open(args.lean_out, "w") as f:
            f.write("\n\n".join(parts) + "\n")
        print("wrote %s" % args.lean_out)
    else:
        for wit in wits:
            print("w=%d n=%d r=%d k=%d d=(%d,%d,%d,%d) sel=%d" % (
                wit["w"], wit["n"], wit["r"], wit["k"],
                wit["d1"], wit["d4"], wit["d3"], wit["dg"], len(wit["selIdx"])))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
