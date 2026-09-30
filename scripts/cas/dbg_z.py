"""Debug: verify Z M = dg I - Gsel Kg (M on right) is solvable."""
import sys
sys.path.insert(0, "/projects/adjquad")
from scripts.cas import emit_witnesses as ew
from sympy import Matrix, eye


def main():
    for w in [4, 6, 14]:
        dom, M = ew.dmat_int(w)
        n = len(dom)
        Mq = Matrix(M)
        S = sorted(Mq.T.rref()[1])
        r = len(S)
        k = n - r
        A = Mq.extract(S, list(range(n)))
        G = (A * A.T).inv()
        Cq = (G * A * Mq.T).T            # n x r
        Ns = Mq.nullspace()
        Nq = Matrix.hstack(*Ns) if Ns else Matrix.zeros(n, 0)
        N, LN = ew._to_int(Nq)
        Kq = (Nq.T * Nq).inv() * Nq.T
        K, d3k = ew._to_int(Kq)
        d3 = d3k * LN
        # Gsel, Kg, dg
        from check_s6 import F0, H, J1, J2, a0, a1, a2, a3, a4, a5
        from sympy import Poly, expand
        gens = [a4, a5, J1, J2, F0, H]
        sel = ew._gen_mono_exps(w)
        ridx = {m: i for i, m in enumerate(dom)}
        Ecols = []
        denoms = [1]
        for exps in sel:
            f = 1
            for g, e in zip(gens, exps):
                f *= g ** e
            d = Poly(expand(f), a0, a1, a2, a3, a4, a5).as_dict()
            col = [ew.Rational(0)] * n
            for key, c in d.items():
                col[ridx[key]] += ew.Rational(c)
            denoms.extend(x.q for x in col)
            Ecols.append(col)
        D0 = 1
        for dd in denoms:
            a, b = D0, dd
            while b:
                a, b = b, a % b
            D0 = D0 * dd // a
        Eq = Matrix(Ecols).T if Ecols else Matrix.zeros(n, 0)
        selIdx = sorted(Eq.rref()[1])
        Esel = Eq.extract(list(range(n)), selIdx)
        Hg = (Esel.T * Esel).inv()
        Kgq = Hg * Esel.T
        Gsel = [[int(ew.Rational(x) * D0) for x in row] for row in Esel.tolist()]
        Kg, LK = ew._to_int(Kgq)
        dg = LK * D0
        print("w=%d n=%d r=%d k=%d dg=%d" % (w, n, r, k, dg))
        Gselq = Matrix(Gsel)
        Kgg = Matrix(Kg)
        # A0' = dg I - Gsel Kg
        A0p = dg * eye(n) - Gselq * Kgg
        print("  Gsel Kg == dg I on col Gsel:", Gselq * Kgg * Gselq == dg * Gselq)
        # Mpinv
        Mpinv = A.T * G * (Cq.T * Cq).inv() * Cq.T
        Zq = A0p * Mpinv
        print("  Z M == dg I - Gsel Kg:", Zq * Mq == A0p)
        # consequence: for x in ker M, dg x == Gsel Kg x
        random = __import__("random"); random.seed(2)
        ok = True
        for _ in range(8):
            c = Matrix([random.randint(-3, 3) for _ in range(k)])
            x = Nq * c   # in ker M
            if dg * x != Gselq * Kgg * x:
                ok = False
                break
        print("  dg x == Gsel Kg x for x in ker M:", ok)


if __name__ == "__main__":
    main()