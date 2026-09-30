"""Independent certificate oracle for emit_witnesses.

No historical pre-producer ModuleNotFoundError evidence is available.

Run: python3 scripts/cas/test_emit_witnesses.py
"""

import os
import sys
from copy import deepcopy
from functools import cache
from itertools import product
from math import lcm, prod

from sympy import Poly

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from emit_witnesses import witness_for_weight
from check_s6 import F0, H, J1, J2, a0, a1, a2, a3, a4, a5, mono_w


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def _matmul(A, B, n, m, p):
    """Multiply checked shapes, retaining the outer shape when m = 0."""
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)]
            for i in range(n)]


def _eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def _rows_of(M, S):
    return [M[i] for i in S]


@cache
def _decoded_columns(w):
    """Re-expand the mathematical generators, never producer Ecols/helpers.

    Enumerate a Cartesian box then filter by weight, independently of the
    producer's remainder loops. Reuse only the algebra's defining polynomials
    and ambient basis order from check_s6.
    """
    dom = mono_w(w)
    gens = (a4, a5, J1, J2, F0, H)
    weights = (24, 14, 4, 6, 1)
    cols = []
    for eh, ef, ej2, ej1, ep in product(*(range(w // d + 1) for d in weights)):
        eq = w - (24 * eh + 14 * ef + 4 * ej2 + 6 * ej1 + ep)
        if eq < 0:
            continue
        exps = (ep, eq, ej1, ej2, ef, eh)
        poly = Poly(prod(g ** e for g, e in zip(gens, exps)),
                    a0, a1, a2, a3, a4, a5)
        cols.append([poly.coeff_monomial(m) for m in dom])
    return cols


def _verify(wit):
    """Check exact decode, shapes, nonzero scales and every witness equation."""
    w, n, r, k = (wit[key] for key in ("w", "n", "r", "k"))
    if not all(type(x) is int and x >= 0 for x in (w, n, r, k)) or r + k != n:
        return False
    if any(type(wit[key]) is not int or wit[key] == 0
           for key in ("d1", "d4", "d3", "dg", "D0", "dL", "dY", "dX", "dB")):
        return False
    shapes = {"M": (n, n), "T": (n, r), "C": (n, r), "N": (n, k),
              "K": (k, n), "Gsel": (n, k), "Kg": (k, n), "L": (r, n),
              "Y": (n, n), "X": (k, k), "B": (n, n)}
    for name, (rows, cols) in shapes.items():
        mat = wit[name]
        if (len(mat) != rows or any(len(row) != cols for row in mat)
                or any(type(x) is not int for row in mat for x in row)):
            return False
    Ecols = _decoded_columns(w)
    if n != len(mono_w(w)) or wit["Ecols"] != Ecols:
        return False
    S, selIdx = wit["S"], wit["selIdx"]
    for indices, count, bound in ((S, r, n), (selIdx, k, len(Ecols))):
        if (len(indices) != count
                or any(type(i) is not int or not 0 <= i < bound for i in indices)
                or len(set(indices)) != count):
            return False
    G, D0 = wit["Gsel"], wit["D0"]
    if D0 != lcm(*(int(c.q) for col in Ecols for c in col)):
        return False
    if any(G[i][j] != D0 * Ecols[s][i]
           for j, s in enumerate(selIdx) for i in range(n)):
        return False
    M = wit["M"]
    T, C, N, K = wit["T"], wit["C"], wit["N"], wit["K"]
    d1, d4, d3 = wit["d1"], wit["d4"], wit["d3"]
    ok = True
    A = _rows_of(M, S)
    ok &= (_matmul(A, T, r, n, r) == [[d1 * x for x in row] for row in _eye(r)])
    ok &= (_matmul(C, A, n, r, n) == [[d4 * x for x in row] for row in M])
    ok &= (_matmul(M, N, n, n, k) == [[0] * k for _ in range(n)])
    ok &= (_matmul(K, N, k, n, k) == [[d3 * x for x in row] for row in _eye(k)])
    G, Kg = wit["Gsel"], wit["Kg"]
    ok &= (_matmul(Kg, G, k, n, k) == [[wit["dg"] * x for x in row] for row in _eye(k)])
    # hker direction 1 (kernel membership): M * Gsel == 0 (exact integers).
    ok &= (_matmul(M, G, n, n, k) == [[0] * k for _ in range(n)])
    # hker left-inverse certificates: L C = dL I_r and Y (A; Kg) = dY I_n.
    ok &= (_matmul(wit["L"], C, r, n, r)
           == [[wit["dL"] * x for x in row] for row in _eye(r)])
    Q = A + wit["Kg"]
    ok &= (_matmul(wit["Y"], Q, n, n, n)
           == [[wit["dY"] * x for x in row] for row in _eye(n)])
    # hker spanning certificates: Gsel X = dX N and M^T B = dB (d3 I - N K).
    X, B = wit["X"], wit["B"]
    ok &= (_matmul(G, X, n, k, k) == [[wit["dX"] * x for x in row] for row in N])
    NK = _matmul(N, K, n, k, n)
    A0 = [[(d3 if i == j else 0) - NK[i][j] for j in range(n)] for i in range(n)]
    Mt = [[M[j][i] for j in range(n)] for i in range(n)]
    ok &= (_matmul(Mt, B, n, n, n) == [[wit["dB"] * x for x in row] for row in A0])
    # Kg G = dg I with dg != 0 already certifies column independence.
    return ok


def _tamper_checks(w0, w1, w4, w14):
    """Reject corrupt actual certificates, not an unrelated lattice example."""
    ok = True
    for key in ("d1", "d4", "d3", "dg", "D0", "dL", "dY", "dX", "dB"):
        bad = deepcopy(w0)
        bad[key] = 0
        ok &= _check("reject zero " + key, not _verify(bad))
    for key in ("M", "T", "C", "N", "K", "Gsel", "Kg", "L", "Y", "X", "B"):
        bad = deepcopy(w4)
        bad[key] = [[0 for _ in row] for row in bad[key]]
        ok &= _check("reject corrupt " + key + " identity", not _verify(bad))
    for key, value in (("S", [-1] + w4["S"][1:]),
                       ("S", [w4["n"]] + w4["S"][1:]),
                       ("selIdx", [-1] + w4["selIdx"][1:]),
                       ("selIdx", [len(w4["Ecols"])] + w4["selIdx"][1:]),
                       ("selIdx", [0] * w4["k"])):
        bad = deepcopy(w4)
        bad[key] = value
        ok &= _check("reject invalid " + key + " " + str(value), not _verify(bad))
    for key, value in (("M", [[0], [0, 0]]), ("N", [[1, 0]]),
                       ("T", []), ("r", 1)):
        bad = deepcopy(w1)
        bad[key] = value
        ok &= _check("reject malformed " + key, not _verify(bad))
    # All product identities still hold after this sign change. A verifier
    # trusting the producer's matching Ecols would accept the wrong decode.
    bad = deepcopy(w1)
    for key in ("Gsel", "Kg", "X", "Y"):
        bad[key] = [[-x for x in row] for row in bad[key]]
    bad["Ecols"] = [[-x for x in col] for col in bad["Ecols"]]
    ok &= _check("reject coordinated false decode", not _verify(bad))
    bad = deepcopy(w14)
    jj = bad["selIdx"].index(54)
    for i, c in enumerate(bad["Ecols"][54]):
        bad["Gsel"][i][jj] = bad["D0"] * int(c)
        bad["Ecols"][54][i] = int(c)
    ok &= _check("reject truncated rational F0 decode", not _verify(bad))
    return ok


def main():
    ok = True
    w0 = witness_for_weight(0)
    ok &= _check("w0 n=1 r=0 k=1", (w0["n"], w0["r"], w0["k"]) == (1, 0, 1))
    ok &= _check("w0 M=[[0]]", w0["M"] == [[0]])
    ok &= _check("w0 N=K=[[1]]", w0["N"] == [[1]] and w0["K"] == [[1]])
    ok &= _check("w0 D0=1", w0["D0"] == 1)
    ok &= _check("w0 verifies", _verify(w0))
    w1 = witness_for_weight(1)
    ok &= _check("w1 n=2 r=0 k=2", (w1["n"], w1["r"], w1["k"]) == (2, 0, 2))
    ok &= _check("w1 M=0, N=K=Gsel=I", w1["M"] == [[0, 0], [0, 0]]
                 and all(w1[key] == _eye(2) for key in ("N", "K", "Gsel")))
    ok &= _check("w1 D0=1", w1["D0"] == 1)
    ok &= _check("w1 verifies", _verify(w1))
    for w in (4, 6, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13):
        wit = witness_for_weight(w)
        if w == 4:
            w4 = wit
        ok &= _check("w%d verifies (decode/kernel/rank/D0)" % w, _verify(wit))
        ok &= _check("w%d D0=1 (integral range)" % w, wit["D0"] == 1)
    # w=14: the first non-integral weight (F0 coefficients 1/3, 1/5, 1/35).
    w14 = witness_for_weight(14)
    ok &= _check("w14 n=236 r=181 k=55", (w14["n"], w14["r"], w14["k"]) == (236, 181, 55))
    ok &= _check("w14 D0=105", w14["D0"] == 105)
    ok &= _check("w14 verifies (exact decode, kernel, rank)", _verify(w14))
    # F0-column regression: the 1/3, 1/5, 1/35 coefficients must survive as
    # 105*(1/3)=35, 105*(-1/5)=-21, 105*(1/35)=3 (truncation would emit 0).
    jj = w14["selIdx"].index(54)
    f0col = [w14["Gsel"][r][jj] for r in range(w14["n"])]
    ok &= _check("w14 F0 column has 35, -21, 3",
                 35 in f0col and (-21) in f0col and 3 in f0col)
    ok &= _tamper_checks(w0, w1, w4, w14)
    print("test_emit_witnesses OK" if ok else "test_emit_witnesses FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
