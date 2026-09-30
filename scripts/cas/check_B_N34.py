"""Check B: N<=4 base + defect + finite-field N=3 (Theorem B, status Established).

Covers the adjacent-quadratic shift discrete map
    P_{lam,N}(a)_n = a_n + lam * a_{n+1} * a_{n+2},  a_{N+1} = a_{N+2} = 0,
and the triangular derivation D_N(a_n) = a_{n+1} * a_{n+2} from check_A.

  N=3 discrete invariant  I_0 = a_0 - a_1^2/(2*a_3) + (lam/2)*a_1*a_2
  N=3 continuous invariant H  = a_0 - a_1^2/(2*a_3)  (lam -> 0 limit)
  Euler gap (N=3)         lam^2/2 * D_3^2(a_0) = lam^2/2 * a_2^2*a_3
  N=4 continuous invariants J0 = 2*a_0*a_3 - a_1^2, J1 = 2*a_1*a_4 - a_2^2
  N=4 first discrete invariant  I_1 = a_1 - a_2^2/(2*a_4) + (lam/2)*a_2*a_3
  N=4 antidifference primitives (u = a_2, c = lam*a_3*a_4, c != 0):
      S_1(u) = (u^2 - c*u)/(2*c)
      S_2(u) = u^3/(3*c) - u^2/2 + c*u/6
      S_3(u) = u^4/(4*c) - u^3/2 + c*u^2/4
  N=4 second discrete invariant
      I_0 = a_0 - lam*I_1*S_1(a_2) - lam/(2*a_4)*S_3(a_2)
            + lam^2*a_3/2*S_2(a_2)
  Commutator, 0-component (see convention note in _check_commutator):
      (P_mu o P_lam - P_lam o P_mu)_0 = lam*mu*(lam - mu)*a_2*a_3^2*a_4
  Finite-field N=3 cycle classification: algebraic proof is in
  paper/02-base.tex; this script re-checks the classification and the exact
  counts by exhaustive enumeration over the tested fields F_3, F_5, F_7,
  F_11, F_2 and F_4 only. Enumeration on its own does not imply all-F_q
  results.

All polynomials above are D-checked below (continuous invariants via
verify_D; discrete invariants via direct substitution).

SymPy-only (+ stdlib). Run:
    python3 scripts/cas/check_B_N34.py  # log: data/cas_check_B.log
Prints PASS/FAIL per check plus a final `check_B OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from check_A import apply_D, verify_D  # noqa: E402
from sympy import expand  # noqa: E402


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return bool(cond)


def _is_zero(expr):
    from sympy import expand

    return expand(expr) == 0


def _check_gap_N3():
    """Euler gap at N=3: exp(lam D_3)(a_0) - P_{lam,3}(a_0)."""
    from sympy import symbols

    ok = True
    N = 3
    a = symbols("a_0:4")
    lam = symbols("lam")
    D1 = apply_D(a[0], a, N)
    ok &= _check("N=3 D(a_0)=a_1*a_2", D1 == a[1] * a[2])
    D2 = apply_D(D1, a, N)
    ok &= _check("N=3 D^2(a_0)=a_2^2*a_3", D2 == a[2] ** 2 * a[3])
    ok &= _check("N=3 D^3(a_0)=0", apply_D(D2, a, N) == 0)
    # Truncated exponential terminates (D^3 = 0 on a_0).
    flow0 = a[0] + lam * D1 + lam**2 / 2 * D2
    discrete0 = a[0] + lam * a[1] * a[2]
    ok &= _check(
        "N=3 Euler gap flow-discrete=lam^2/2*a_2^2*a_3",
        _is_zero(flow0 - discrete0 - lam**2 / 2 * a[2] ** 2 * a[3]),
    )
    ok &= _check(
        "N=3 gap nonzero (discrete!=exp on generators)",
        expand(flow0 - discrete0) != 0,
    )
    return ok


def _check_H_N3():
    """N=3 continuous invariant H and discrete invariant I_0."""
    from sympy import expand, symbols

    ok = True
    N = 3
    a = symbols("a_0:4")
    lam = symbols("lam")
    H = a[0] - a[1] ** 2 / (2 * a[3])
    ok &= _check("N=3 verify_D(H)", verify_D(H, a, N) is True)
    # Discrete invariance by direct substitution. N=3 update fixes a_2, a_3:
    # b_0 = a_0 + lam a_1 a_2, b_1 = a_1 + lam a_2 a_3, b_3 = a_3.
    b0 = a[0] + lam * a[1] * a[2]
    b1 = a[1] + lam * a[2] * a[3]
    I0 = a[0] - a[1] ** 2 / (2 * a[3]) + lam / 2 * a[1] * a[2]
    I0p = b0 - b1**2 / (2 * a[3]) + lam / 2 * b1 * a[2]
    ok &= _check("N=3 discrete I_0 P-invariant", _is_zero(I0p - I0))
    ok &= _check(
        "N=3 I_0 lam->0 limit is H", _is_zero(expand(I0.subs(lam, 0) - H))
    )
    return ok


def _check_continuous_N4():
    """N=4 continuous (D_4) invariants, polynomial and divided forms."""
    from sympy import symbols

    ok = True
    N = 4
    a = symbols("a_0:5")
    J0 = 2 * a[0] * a[3] - a[1] ** 2
    J1 = 2 * a[1] * a[4] - a[2] ** 2
    ok &= _check("N=4 verify_D(2a0a3-a1^2)", verify_D(J0, a, N) is True)
    ok &= _check("N=4 verify_D(2a1a4-a2^2)", verify_D(J1, a, N) is True)
    ok &= _check(
        "N=4 verify_D(a0-a1^2/2a3)", verify_D(a[0] - a[1] ** 2 / (2 * a[3]), a, N) is True
    )
    ok &= _check(
        "N=4 verify_D(a1-a2^2/2a4)", verify_D(a[1] - a[2] ** 2 / (2 * a[4]), a, N) is True
    )
    return ok


def _check_defect_N4():
    """N=4 discrete-vs-continuous defect: full D_4 orbit of a_0."""
    from sympy import symbols

    ok = True
    N = 4
    a = symbols("a_0:5")
    lam = symbols("lam")
    D1 = apply_D(a[0], a, N)
    D2 = apply_D(D1, a, N)
    D3 = apply_D(D2, a, N)
    D4 = apply_D(D3, a, N)
    D5 = apply_D(D4, a, N)
    ok &= _check("N=4 D^2(a_0)=a_2^2a_3+a_1a_3a_4", D2 == a[2] ** 2 * a[3] + a[1] * a[3] * a[4])
    ok &= _check("N=4 D^3(a_0)=3a_2a_3^2a_4", D3 == 3 * a[2] * a[3] ** 2 * a[4])
    ok &= _check("N=4 D^4(a_0)=3a_3^3a_4^2", D4 == 3 * a[3] ** 3 * a[4] ** 2)
    ok &= _check("N=4 D^5(a_0)=0", D5 == 0)
    flow0 = (
        a[0]
        + lam * D1
        + lam**2 / 2 * D2
        + lam**3 / 6 * D3
        + lam**4 / 24 * D4
    )
    discrete0 = a[0] + lam * a[1] * a[2]
    ok &= _check(
        "N=4 lam^2 defect coefficient nonzero",
        _is_zero(lam**2 / 2 * D2) is False,
    )
    ok &= _check(
        "N=4 discrete!=exp (gap nonzero)", expand(flow0 - discrete0) != 0
    )
    return ok


def _check_discrete_N4():
    """N=4 discrete invariants I_1 and I_0 (S-form), plus S identities."""
    from sympy import symbols

    ok = True
    a = symbols("a_0:5")
    lam = symbols("lam")
    u, c = symbols("u c")
    # Antidifference identities Delta_c S_k(u) = u^k (char 0, c != 0 formal).
    S1 = (u**2 - c * u) / (2 * c)
    S2 = u**3 / (3 * c) - u**2 / 2 + c * u / 6
    S3 = u**4 / (4 * c) - u**3 / 2 + c * u**2 / 4
    for k, S in ((1, S1), (2, S2), (3, S3)):
        ok &= _check(
            "N=4 Delta_c S_%d(u)=u^%d" % (k, k),
            _is_zero(S.subs(u, u + c) - S - u**k),
        )
    # N=4 update: b_3 = a_3, b_4 = a_4, so c' = c with c = lam a_3 a_4.
    b0 = a[0] + lam * a[1] * a[2]
    b1 = a[1] + lam * a[2] * a[3]
    b2 = a[2] + lam * a[3] * a[4]
    I1 = a[1] - a[2] ** 2 / (2 * a[4]) + lam / 2 * a[2] * a[3]
    I1p = b1 - b2**2 / (2 * a[4]) + lam / 2 * b2 * a[3]
    ok &= _check("N=4 discrete I_1 P-invariant", _is_zero(I1p - I1))
    s1 = (a[2] ** 2 - lam * a[3] * a[4] * a[2]) / (2 * lam * a[3] * a[4])
    s2 = (
        a[2] ** 3 / (3 * lam * a[3] * a[4])
        - a[2] ** 2 / 2
        + lam * a[3] * a[4] * a[2] / 6
    )
    s3 = a[2] ** 4 / (4 * lam * a[3] * a[4]) - a[2] ** 3 / 2 + lam * a[3] * a[4] * a[2] ** 2 / 4
    I0 = a[0] - lam * I1 * s1 - lam / (2 * a[4]) * s3 + lam**2 * a[3] / 2 * s2
    t1 = (b2**2 - lam * a[3] * a[4] * b2) / (2 * lam * a[3] * a[4])
    t2 = b2**3 / (3 * lam * a[3] * a[4]) - b2**2 / 2 + lam * a[3] * a[4] * b2 / 6
    t3 = b2**4 / (4 * lam * a[3] * a[4]) - b2**3 / 2 + lam * a[3] * a[4] * b2**2 / 4
    I0p = b0 - lam * I1p * t1 - lam / (2 * a[4]) * t3 + lam**2 * a[3] / 2 * t2
    ok &= _check("N=4 discrete I_0 (S-form) P-invariant", _is_zero(I0p - I0))
    return ok


def _check_commutator():
    """Commutator 0-component at N=4.

    Convention: [P_lam, P_mu]_0 denotes the ordered point difference
    (P_mu o P_lam - P_lam o P_mu)_0, i.e. apply lam first, then mu,
    minus the reverse order. With this ordering the difference equals
    lam*mu*(lam - mu)*a_2*a_3^2*a_4; the reverse ordering gives its
    negation. Components 1..4 vanish in both orders.
    """
    from sympy import symbols

    ok = True
    a = symbols("a_0:5")
    lam, mu = symbols("lam mu")

    def step(state, t):
        s0, s1, s2, s3, s4 = state
        return [s0 + t * s1 * s2, s1 + t * s2 * s3, s2 + t * s3 * s4, s3, s4]

    lam_then_mu = step(step(a, lam), mu)  # P_mu o P_lam
    mu_then_lam = step(step(a, mu), lam)  # P_lam o P_mu
    gap0 = expand(lam_then_mu[0] - mu_then_lam[0])
    ok &= _check(
        "N=4 commutator [P_lam,P_mu]_0=lam mu(lam-mu)a2a3^2a4",
        _is_zero(gap0 - lam * mu * (lam - mu) * a[2] * a[3] ** 2 * a[4]),
    )
    for i in (1, 2, 3, 4):
        ok &= _check(
            "N=4 commutator component %d vanishes" % i,
            expand(lam_then_mu[i] - mu_then_lam[i]) == 0,
        )
    return ok


# --- Finite-field N=3 enumeration (tested fields only) ----------------------


def _orbit_len_prime(a, lam, p):
    """Orbit length of a = (a0..a3) under P_{lam,3} over F_p (lam != 0)."""
    cur = tuple(x % p for x in a)
    start = cur
    for k in range(1, 5 * p + 5):
        a0, a1, a2, a3 = cur
        cur = ((a0 + lam * a1 * a2) % p, (a1 + lam * a2 * a3) % p, a2, a3)
        if cur == start:
            return k
    raise AssertionError("orbit did not close")


def _predicted_len(a0, a1, a2, a3, lam, p):
    c = (lam * a2 * a3) % p
    d = (lam * a1 * a2) % p
    if c == 0:
        return 1 if d == 0 else p
    return p if p % 2 == 1 else 4


def _check_prime_field(p):
    import itertools

    from sympy import symbols  # noqa: F401  (keeps SymPy-only discipline explicit)

    ok = True
    q = p
    lam = 1
    nfix = 0
    n_c0_cycles = 0
    n_c1_cycles = 0
    bad = 0
    for a in itertools.product(range(p), repeat=4):
        a0, a1, a2, a3 = a
        if _orbit_len_prime(a, lam, p) != _predicted_len(a0, a1, a2, a3, lam, p):
            bad += 1
    ok &= _check("F_%d all orbits match classification" % p, bad == 0)
    # Exact counts (lam != 0): fixed q^3 + q(q-1); c=0 stratum holds
    # q(q-1)^2 points in length-p cycles; c!=0 stratum holds (q-1)^2 q^2
    # points in length-L cycles with L = p (p odd) or 4 (p = 2).
    L = p if p % 2 == 1 else 4
    for a in itertools.product(range(p), repeat=4):
        a0, a1, a2, a3 = a
        c = (lam * a2 * a3) % p
        d = (lam * a1 * a2) % p
        leng = _orbit_len_prime(a, lam, p)
        if leng == 1:
            nfix += 1
        elif c == 0:
            n_c0_cycles += 1
        else:
            n_c1_cycles += 1
    ok &= _check(
        "F_%d fixed count q^3+q(q-1)=%d" % (p, q**3 + q * (q - 1)),
        nfix == q**3 + q * (q - 1),
    )
    ok &= _check(
        "F_%d c=0 cycle points q(q-1)^2=%d" % (p, q * (q - 1) ** 2),
        n_c0_cycles == q * (q - 1) ** 2 and n_c0_cycles % p == 0,
    )
    ok &= _check(
        "F_%d c!=0 cycle points (q-1)^2q^2=%d over L=%d"
        % (p, (q - 1) ** 2 * q**2, L),
        n_c1_cycles == (q - 1) ** 2 * q**2 and n_c1_cycles % L == 0,
    )
    return ok


class _GF4:
    """F_4 = F_2[t]/(t^2+t+1); elements 0,1,w,w+1 coded 0..3."""

    @staticmethod
    def add(x, y):
        return x ^ y

    @staticmethod
    def mul(x, y):
        if x == 0 or y == 0:
            return 0
        x0, x1 = x & 1, (x >> 1) & 1
        y0, y1 = y & 1, (y >> 1) & 1
        c0 = x0 & y0
        c1 = (x0 & y1) ^ (x1 & y0)
        c2 = x1 & y1
        return (c0 ^ c2) | ((c1 ^ c2) << 1)


def _check_F4():
    import itertools

    ok = True
    add, mul = _GF4.add, _GF4.mul

    def step(a):
        a0, a1, a2, a3 = a
        return (add(a0, mul(mul(1, a1), a2)), add(a1, mul(mul(1, a2), a3)), a2, a3)

    def orbit_len(a):
        cur, start = a, a
        for k in range(1, 9):
            cur = step(cur)
            if cur == start:
                return k
        raise AssertionError("F_4 orbit did not close")

    bad = nfix = n_c0 = n_c1 = 0
    for a in itertools.product(range(4), repeat=4):
        a0, a1, a2, a3 = a
        c = mul(a2, a3)
        d = mul(a1, a2)
        pred = 1 if (c == 0 and d == 0) else (2 if c == 0 else 4)
        leng = orbit_len(a)
        if leng != pred:
            bad += 1
        if leng == 1:
            nfix += 1
        elif c == 0:
            n_c0 += 1
        else:
            n_c1 += 1
    ok &= _check("F_4 all orbits match classification", bad == 0)
    ok &= _check("F_4 fixed count q^3+q(q-1)=76", nfix == 4**3 + 4 * 3)
    ok &= _check("F_4 c=0 cycle points q(q-1)^2=36", n_c0 == 4 * 9 and n_c0 % 2 == 0)
    ok &= _check("F_4 c!=0 cycle points (q-1)^2q^2=144 over L=4", n_c1 == 9 * 16 and n_c1 % 4 == 0)
    return ok


def main():
    ok = True
    ok &= _check_gap_N3()
    ok &= _check_H_N3()
    ok &= _check_continuous_N4()
    ok &= _check_defect_N4()
    ok &= _check_discrete_N4()
    ok &= _check_commutator()
    for p in (3, 5, 7, 11, 2):
        ok &= _check_prime_field(p)
    ok &= _check_F4()
    print("check_B OK" if ok else "check_B FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
