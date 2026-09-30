# Debug: why does M^T B' = d3 I - N K fail? (w=4)
import sys
from sympy import Matrix, eye

sys.path.insert(0, ".")
from scripts.cas import emit_witnesses as ew
from check_s6 import F0, H, J1, J2, a0, a1, a2, a3, a4, a5


def main():
    w = int(sys.argv[1])
    dom, M = ew.dmat_int(w)
    n = len(dom)
    Mq = Matrix(M)
    S = sorted(Mq.T.rref()[1])
    r = len(S)
    k = n - r
    A = Mq.extract(S, list(range(n)))
    G = (A * A.T).inv()
    Cq = (G * A * Mq.T).T
    Ns = Mq.nullspace()
    Nq = Matrix.hstack(*Ns)          # n x k
    H = (Nq.T * Nq).inv()
    Kq = H * Nq.T                    # k x n
    N, LN = ew._to_int(Nq)           # scaled integer n x k
    K, d3k = ew._to_int(Kq)          # scaled integer k x n
    d3 = d3k * LN
    print("w=%d n=%d r=%d k=%d LN=%d d3=%d" % (w, n, r, k, LN, d3))
    print("K N == d3 I:", Matrix(K) * Matrix(N) == d3 * eye(k))
    # A0 in the CONSISTENT (scaled) form:
    A0 = d3 * eye(n) - Matrix(N) * Matrix(K)
    print("A0 integral:", all(x.is_Integer for x in A0))
    print("M N == 0:", Mq * Matrix(N) == Matrix.zeros(n, k))
    # does A0 kill ker M (N cols)?
    bad = 0
    for j in range(k):
        if A0 * Nq[:, j] != Matrix.zeros(n, 1):
            bad += 1
    print("A0 kills N cols:", k - bad, "of", k)
    # im A0 vs col M^T
    rA0 = A0.rank()
    rMT = Mq.T.rank()
    rboth = Matrix.hstack(A0, Mq.T).rank()
    print("rank A0:", rA0, " rank M^T:", rMT, " rank[A0|M^T]:", rboth,
          " im A0 subset col M^T ?", rboth == rMT)
    # the B' I used: d4 Cq G A A0
    C, d4 = ew._to_int(Cq)
    Bq = d4 * Cq * G * A * A0
    print("Bq shape:", Bq.shape)
    print("M^T B' == A0:", Mq.T * Bq == A0)
    # alternative: A0 = M^T B' needs col A0 in col M^T; if not, try A0 = M B''?
    rboth2 = Matrix.hstack(A0, Mq).rank()
    print("rank[A0|M]:", rboth2, " im A0 subset col M ?", rboth2 == Mq.rank())


if __name__ == "__main__":
    main()