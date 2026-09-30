"""Stage-1 port (N=5 formalization, Batch A): base checks 1.1-1.5 (SymPy).

Covers:
  1.1: R=QQ[a0..a5], D as given, J1/J2/F0 exact; assert D=0.
  1.2: Fibonacci weights {8,5,3,2,1,1}; assert J1 wt 6, J2 wt 4, F0 wt 14
       (every monomial).
  1.3: Jacobian of [a4,a5,J1,J2,F0] w.r.t. [a1..a5]; assert det != 0 as
       polynomial and report factored form.
  1.4 (REWRITTEN from scratch, NOT a transliteration of the prompt's broken
       S1.4): the prompt's sketch (coefficient extraction via
       term.coefficient({...}) and term/coeff) does not yield monomial parts
       and its predicted-line logic is incoherent. Here: for each weight w,
       build the FULL monomial basis of the graded piece, build the matrix
       of D restricted to that piece over QQ with exact rational arithmetic
       (stdlib Fractions), compute dim ker exactly via sparse Gaussian
       elimination, and compare against coeff of t^w in
       1/((1-t)^2(1-t^4)(1-t^6)(1-t^14)). Print per-weight
       computed/predicted/match. "Even-equivalent" is interpreted as every
       integer w in range (even-only subset included); full 0..30 completes
       in seconds, so no shrink to 0..24 was needed.
  1.5: G0=F0-a4^2a5^4a0; assert G0|_{a4=0} != 0 and G0|_{a5=0} != 0, report
       both remainders.

Run:
    mkdir -p data/formalize
    python3 scripts/cas/check_stage1.py  # log: data/formalize/stage1.log
Prints PASS/FAIL per check plus a final `stage1 OK` on success
(`stage1 FAILED` otherwise; exit 0/1).
"""

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name, flush=True)
    return bool(cond)


def _is_zero(expr):
    from sympy import cancel, expand

    if expand(expr) == 0:
        return True
    return cancel(expr) == 0


FIB_WTS = (8, 5, 3, 2, 1, 1)
WMAX_FULL = 30


def _vars():
    from sympy import symbols

    return symbols("a_0:6")


def _gens(a):
    a0, a1, a2, a3, a4, a5 = a
    J1 = 2 * a1 * a4 - a2**2
    J2 = 2 * a2 * a5 - a3**2
    F0 = (
        a4**2 * a5**4 * a0
        - a4 * a5**3 * a3 * a2 * a1
        + a4 * a5**2 * a3**3 * a1 / 3
        + a5**2 * a3**3 * a2**2 / 3
        - a5 * a3**5 * a2 / 5
        + a3**7 / 35
    )
    return J1, J2, F0


def _check_11(a, N, J1, J2, F0):
    ok = True
    ok &= _check("1.1 D(J1)=0", apply_D(J1, a, N) == 0)
    ok &= _check("1.1 D(J2)=0", apply_D(J2, a, N) == 0)
    ok &= _check("1.1 D(F0)=0", apply_D(F0, a, N) == 0)
    ok &= _check("1.1 verify_D(J1)", verify_D(J1, a, N) is True)
    ok &= _check("1.1 verify_D(J2)", verify_D(J2, a, N) is True)
    ok &= _check("1.1 verify_D(F0)", verify_D(F0, a, N) is True)
    return ok


def _wt_of_mon(exps):
    return sum(e * w for e, w in zip(exps, FIB_WTS))


def _check_12(a, J1, J2, F0):
    from sympy import Poly

    ok = True
    cases = [("J1", J1, 6), ("J2", J2, 4), ("F0", F0, 14)]
    for name, poly, want in cases:
        monoms = Poly(poly, *a).monoms()
        wts = sorted(_wt_of_mon(e) for e in monoms)
        ok &= _check(
            "1.2 %s every monomial wt %d (got %s)" % (name, want, wts),
            all(w == want for w in wts),
        )
    return ok


def _check_13(a, J1, J2, F0):
    from sympy import Matrix, expand, factor

    ok = True
    a0, a1, a2, a3, a4, a5 = a
    gens = [a4, a5, J1, J2, F0]
    cols = [a1, a2, a3, a4, a5]
    M = Matrix([[g.diff(c) for c in cols] for g in gens])
    det = expand(M.det())
    fac = factor(det)
    print("1.3 det factored form: %s" % fac, flush=True)
    print("1.3 det expanded form: %s" % det, flush=True)
    ok &= _check("1.3 det != 0 as polynomial", det != 0)
    ok &= _check(
        "1.3 det == -4*a1*a2*a4^2*a5^4",
        expand(det + 4 * a1 * a2 * a4**2 * a5**4) == 0,
    )
    # Generic full rank witness (supports independence claim).
    pt = dict(zip(a, (0, 1, 2, 3, 4, 5)))
    full = Matrix([[g.diff(c) for c in a] for g in gens])
    ok &= _check("1.3 Jacobian rank 5 at sample point", full.subs(pt).rank() == 5)
    return ok


def _monomial_basis(w):
    """FULL monomial basis of the weight-w graded piece as exponent tuples.

    Weights (a0..a5) = (8,5,3,2,1,1). Enumerates every (e0..e5) with
    sum e_i*w_i == w. Complete by construction (bounded loops cover all).
    """
    out = []
    wt0, wt1, wt2, wt3 = 8, 5, 3, 2
    for e0 in range(w // wt0 + 1):
        r0 = w - e0 * wt0
        for e1 in range(r0 // wt1 + 1):
            r1 = r0 - e1 * wt1
            for e2 in range(r1 // wt2 + 1):
                r2 = r1 - e2 * wt2
                for e3 in range(r2 // wt3 + 1):
                    rem = r2 - e3 * wt3
                    # e4+e5 == rem (both weight 1).
                    for e4 in range(rem + 1):
                        e5 = rem - e4
                        out.append((e0, e1, e2, e3, e4, e5))
    return out


def _predicted_coeffs(wmax):
    """Exact coeffs of 1/((1-t)^2(1-t^4)(1-t^6)(1-t^14)) via integer DP."""
    gen_wts = [1, 1, 4, 6, 14]
    dp = [0] * (wmax + 1)
    dp[0] = 1
    for gw in gen_wts:
        ndp = [0] * (wmax + 1)
        for i in range(wmax + 1):
            s = 0
            k = 0
            while k * gw <= i:
                s += dp[i - k * gw]
                k += 1
            ndp[i] = s
        dp = ndp
    return dp


def _kernel_dim_exact(w):
    """Dim ker(D|_{V_w}) exactly over QQ.

    D(a0)=a1a2, D(a1)=a2a3, D(a2)=a3a4, D(a3)=a4a5, D(a4)=D(a5)=0, so for
    m = prod a_i^{e_i}:
      D(m) = e0*m/a0*a1a2 + e1*m/a1*a2a3 + e2*m/a2*a3a4 + e3*m/a3*a4a5.
    Each image monomial has the same Fibonacci weight (8=5+3, 5=3+2,
    3=2+1, 2=1+1), so D restricts to V_w -> V_w. Coefficients are the
    exact integers e_i. Rank over QQ is computed by sparse Gaussian
    elimination with stdlib Fractions (exact rational arithmetic).
    Returns (n, rank, nulldim).
    """
    basis = _monomial_basis(w)
    idx = {e: i for i, e in enumerate(basis)}
    n = len(basis)
    rows = [dict() for _ in range(n)]
    for j, (e0, e1, e2, e3, e4, e5) in enumerate(basis):
        if e0 > 0:
            t = (e0 - 1, e1 + 1, e2 + 1, e3, e4, e5)
            i = idx[t]
            rows[i][j] = rows[i].get(j, 0) + e0
        if e1 > 0:
            t = (e0, e1 - 1, e2 + 1, e3 + 1, e4, e5)
            i = idx[t]
            rows[i][j] = rows[i].get(j, 0) + e1
        if e2 > 0:
            t = (e0, e1, e2 - 1, e3 + 1, e4 + 1, e5)
            i = idx[t]
            rows[i][j] = rows[i].get(j, 0) + e2
        if e3 > 0:
            t = (e0, e1, e2, e3 - 1, e4 + 1, e5 + 1)
            i = idx[t]
            rows[i][j] = rows[i].get(j, 0) + e3
    # Exact sparse forward elimination (rank only; columns < col are done).
    qrows = [{k: Fraction(v) for k, v in r.items()} for r in rows]
    rank = 0
    for col in range(n):
        piv = None
        for i in range(rank, n):
            if qrows[i].get(col, 0) != 0:
                piv = i
                break
        if piv is None:
            continue
        qrows[rank], qrows[piv] = qrows[piv], qrows[rank]
        pv = qrows[rank][col]
        for i in range(rank + 1, n):
            v = qrows[i].get(col, 0)
            if v != 0:
                f = v / pv
                pr = qrows[rank]
                ri = qrows[i]
                for k, val in list(pr.items()):
                    if k < col:
                        continue
                    nv = ri.get(k, Fraction(0)) - f * val
                    if nv == 0:
                        if k in ri:
                            del ri[k]
                    else:
                        ri[k] = nv
        rank += 1
    return n, rank, n - rank


def _check_14():
    ok = True
    t_start = time.time()
    wmax = WMAX_FULL
    pred = _predicted_coeffs(wmax)
    print(
        "1.4 exact QQ kernel survey: full monomial basis + sparse "
        "Fraction elimination (rewritten §1.4), range 0..%d" % wmax,
        flush=True,
    )
    all_match = True
    for w in range(wmax + 1):
        t0 = time.time()
        n, rank, nulldim = _kernel_dim_exact(w)
        dt = time.time() - t0
        match = nulldim == pred[w]
        all_match &= match
        print(
            "1.4 w=%d computed=%d predicted=%d match=%s (dim V=%d rank=%d %.2fs)"
            % (w, nulldim, pred[w], match, n, rank, dt),
            flush=True,
        )
        ok &= _check("1.4 w=%d ker==predicted(%d)" % (w, pred[w]), match)
        # Wall-time cap ~15 min: abort gracefully (report partial range).
        if time.time() - t_start > 15 * 60:
            print("1.4 WALL-TIME CAP: stopping early at w=%d" % w, flush=True)
            print("1.4 RANGE SHRUNK due to wall-time (see log)", flush=True)
            break
    else:
        print("1.4 full range 0..%d completed (no shrink needed)" % wmax, flush=True)
    total = time.time() - t_start
    print("1.4 total wall-time %.1fs" % total, flush=True)
    if not all_match:
        print(
            "1.4 NOTE: mismatches at w>=24 (computed > predicted); "
            "see stage1 report (mathematical finding, not a script bug)",
            flush=True,
        )
    return ok


def _check_15(a, F0):
    from sympy import expand

    ok = True
    a0, a1, a2, a3, a4, a5 = a
    G0 = expand(F0 - a4**2 * a5**4 * a0)
    r4 = expand(G0.subs(a4, 0))
    r5 = expand(G0.subs(a5, 0))
    print("1.5 G0|_{a4=0} = %s" % r4, flush=True)
    print("1.5 G0|_{a5=0} = %s" % r5, flush=True)
    ok &= _check("1.5 G0|_{a4=0} != 0", r4 != 0)
    ok &= _check("1.5 G0|_{a5=0} != 0", r5 != 0)
    return ok


def main():
    ok = True
    N = 5
    a = _vars()
    J1, J2, F0 = _gens(a)
    print("== 1.1 D-invariance ==", flush=True)
    ok &= _check_11(a, N, J1, J2, F0)
    print("== 1.2 Fibonacci weights ==", flush=True)
    ok &= _check_12(a, J1, J2, F0)
    print("== 1.3 Jacobian ==", flush=True)
    ok &= _check_13(a, J1, J2, F0)
    print("== 1.4 graded kernel survey ==", flush=True)
    ok &= _check_14()
    print("== 1.5 G0 nonvanishing ==", flush=True)
    ok &= _check_15(a, F0)
    print("stage1 OK" if ok else "stage1 FAILED", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
