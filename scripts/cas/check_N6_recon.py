"""Phase 0 RECON for N=6. Predictions and evidence only - NEVER cited as results.

Every output line is tagged RECON. Nothing here is a theorem, a proof, or a
result; all generator-degree claims below are guesses for Phase 1 to prove
from scratch.

Part A (prediction): the expected N=6 degree row [12, 7, 4, 2] from the
Fibonacci recurrence e_m = F_{m+3} - 1 with m = N-2-k.

Part B (evidence): a Hilbert probe of B = k[a_1, ..., a_6]^D, where D is the
adjacent-quadratic shift D(a_n) = a_{n+1} * a_{n+2} (a_7 = a_8 = 0) shared
with check_A. For each degree d = 1..DEG_MAX the probe builds the SymPy
matrix of D: V_d -> V_{d+1} (V_d = degree-d homogeneous piece of
k[a_1..a_6]), takes its kernel, and greedily separates decomposable
products of previously guessed generators from genuinely new directions.
New directions are GUESSES, not generators, until Phase 1 proves them.

Wall-time discipline: the probe runs SymPy only, with a per-degree alarm
and a global budget (see PER_DEGREE_BUDGET_S / GLOBAL_BUDGET_S). Any stall
is logged as a RECON STALL line (command + matrix size + elapsed + error)
and the script still ships Part A with exit status 0.
"""

import os
import signal
import sys
import time
from functools import reduce
from itertools import combinations_with_replacement
from operator import mul

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
from check_A import apply_D, verify_D

import sympy as sp

N = 6
DEG_MAX = 8
PER_DEGREE_BUDGET_S = 300
GLOBAL_BUDGET_S = 540


class _ProbeTimeout(Exception):
    pass


def _alarm_handler(signum, frame):
    raise _ProbeTimeout("per-degree alarm fired")


def fib(n):
    a, b = 1, 1
    for _ in range(n - 1):
        a, b = b, a + b
    return a


VARS = sp.symbols("a_0:7")  # (a_0, ..., a_6); B uses a_1..a_6
B = list(VARS[1:])


def _mon(c):
    return reduce(mul, [B[i] for i in c], sp.Integer(1))


def _basis(e):
    return [_mon(c) for c in combinations_with_replacement(range(6), e)]


def _coord_mat(exprs, bs):
    """Coordinate matrix of exprs in monomial basis bs (exact, via Poly)."""
    idx = {sp.Poly(m, *B).terms()[0][0]: j for j, m in enumerate(bs)}
    M = sp.zeros(len(bs), len(exprs))
    for j, e in enumerate(exprs):
        for exp, c in sp.Poly(sp.expand(e), *B).terms():
            if c != 0:
                M[idx[exp], j] = c
    return M


def _kernel_basis(d):
    """Basis of ker(D | V_d) as column vectors in the monomial basis."""
    md = _basis(d)
    md1 = _basis(d + 1)
    A = _coord_mat([sp.expand(apply_D(m, VARS, N)) for m in md], md1)
    return md, A, A.nullspace()


def _weighted_count(degs, d):
    """Number of monomials of weighted degree d in weights degs."""
    if not degs:
        return 1 if d == 0 else 0
    first, rest = degs[0], degs[1:]
    return sum(_weighted_count(rest, d - first * e) for e in range(d // first + 1))


def main():
    t0 = time.monotonic()

    # ---- Part A: Fibonacci row prediction (RECON) ----
    # e_m = F_{m+3} - 1, m = N-2-k
    row = [fib((4 - k) + 3) - 1 for k in range(4)]
    assert row == [12, 7, 4, 2], row
    print("PASS predicted N=6 degree row", row)
    print("RECON prediction (not a result): N=6 degree row", row,
          "from e_m = F_{m+3} - 1")

    # ---- Part B: Hilbert probe of B = k[a_1..a_6]^D (RECON evidence) ----
    print("RECON probe: B = k[a_1..a_6]^D with D(a_n) = a_{n+1}*a_{n+2}, "
          "a_7 = a_8 = 0; kernel dims of D: V_d -> V_{d+1}")
    gens = []  # list of (degree, expr) GUESSES
    kerdims = {}
    stalled = False
    for d in range(1, DEG_MAX + 1):
        if time.monotonic() - t0 > GLOBAL_BUDGET_S:
            print("RECON STALL command=check_N6_recon degree=%d size=? "
                  "elapsed=%.1fs error=global-budget-exceeded" % (d, time.monotonic() - t0))
            stalled = True
            break
        md = _basis(d)
        in_dim, out_dim = len(md), len(_basis(d + 1))
        t_deg = time.monotonic()
        prev = signal.signal(signal.SIGALRM, _alarm_handler)
        signal.alarm(PER_DEGREE_BUDGET_S)
        try:
            md, A, K = _kernel_basis(d)
            kerdims[d] = len(K)
            for v in K:  # every kernel direction must really be D-invariant
                assert verify_D(sum(c * m for c, m in zip(v, md)), VARS, N)
            # Decomposable span: products of previously guessed generators
            # of total degree d (products of invariants are invariant).
            prods = set()

            def rec(i, rem, acc):
                if rem == 0:
                    prods.add(sp.expand(acc))
                    return
                for j in range(i, len(gens)):
                    if gens[j][0] <= rem:
                        rec(j, rem - gens[j][0], acc * gens[j][1])

            rec(0, d, sp.Integer(1))
            prods.discard(sp.Integer(1))
            for p in prods:
                assert verify_D(p, VARS, N)
            P = _coord_mat(list(prods), md) if prods else sp.zeros(len(md), 0)
            r = P.rank()
            KK = sp.Matrix.hstack(*K) if K else sp.zeros(len(md), 0)
            R = P.row_join(KK).rank() if K else r
            assert R == len(K)
            new = R - r
            print("RECON probe degree=%d in=%d out=%d kerdim=%d nprods=%d "
                  "decomp-rank=%d new-guess=%d elapsed=%.1fs"
                  % (d, in_dim, out_dim, len(K), len(prods), r, new,
                     time.monotonic() - t_deg))
            if new > 0:  # record representative GUESSES for higher products
                Q = P
                for v in K:
                    if Q.shape[1] == 0 or Q.row_join(v).rank() > Q.rank():
                        Q = v if Q.shape[1] == 0 else Q.row_join(v)
                        g = sum(c * m for c, m in zip(v, md))
                        assert verify_D(g, VARS, N)
                        gens.append((d, sp.expand(g)))
                        if Q.rank() >= R:
                            break
        except _ProbeTimeout as exc:
            print("RECON STALL command=check_N6_recon degree=%d in=%d out=%d "
                  "elapsed=%.1fs error=%s" % (d, in_dim, out_dim,
                                              time.monotonic() - t_deg, exc))
            stalled = True
            signal.alarm(0)
            signal.signal(signal.SIGALRM, prev)
            break
        except Exception as exc:  # log, do not hide: ship Part A alone
            print("RECON STALL command=check_N6_recon degree=%d in=%d out=%d "
                  "elapsed=%.1fs error=%r" % (d, in_dim, out_dim,
                                              time.monotonic() - t_deg, exc))
            stalled = True
            signal.alarm(0)
            signal.signal(signal.SIGALRM, prev)
            break
        finally:
            try:
                signal.alarm(0)
                signal.signal(signal.SIGALRM, prev)
            except Exception:
                pass

    if gens:
        degs = sorted(g for g, _ in gens)
        print("RECON GUESS (not a result): B=k[a_1..a_6]^D appears to need "
              "%d generators of degrees %s" % (len(gens), degs))
        for gdeg, g in gens:
            s = str(g)
            print("RECON guessed-generator degree=%d nterms=%d verify_D=%s %s"
                  % (gdeg, len(sp.Poly(g, *B).terms()), verify_D(g, VARS, N),
                     ("expr=" + s) if len(s) <= 200 else "lead=" + s[:200]))
        # Consistency evidence: kernel dims vs weighted-monomial counts.
        match = all(kerdims[d] == _weighted_count(degs, d) for d in kerdims)
        print("RECON Hilbert-consistency kerdims=%s weighted-counts=%s match=%s"
              % ([kerdims[d] for d in sorted(kerdims)],
                 [_weighted_count(degs, d) for d in sorted(kerdims)], match))
    elif not stalled:
        print("RECON probe: no new generator directions guessed to degree",
              DEG_MAX)
    print("RECON done stalled=%s elapsed=%.1fs; all of the above is evidence "
          "only, never cited as results" % (stalled, time.monotonic() - t0))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
