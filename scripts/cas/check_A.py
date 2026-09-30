"""Check A: core SymPy CAS harness for the adjacent-quadratic shift.

Canonical derivation (see README)::

    D_N(a_n) = a_{n+1} * a_{n+2},   a_{N+1} = a_{N+2} = 0,

on A_N = k[a_0, ..., a_N] (char 0). This module provides the shared
helpers consumed by later checks (Tasks 3+):

    apply_D(poly, vars, N)  -- apply D_N to a polynomial via the chain rule
    verify_D(poly, vars, N) -- True iff D_N(poly) is identically zero

``vars`` is the ordered sequence (a_0, ..., a_N), length N+1, so N is
general. Self-test: ``python3 scripts/cas/check_A.py`` prints PASS lines
and a final ``harness OK`` (exit status 0); any failure prints FAIL and
exits nonzero.
"""

from sympy import expand, sympify


def apply_D(poly, vars, N):
    """Return D_N(poly) where D_N(a_n) = a_{n+1}*a_{n+2} (a_{N+1}=a_{N+2}=0).

    Args:
        poly: SymPy expression in vars (constants allowed).
        vars: sequence (a_0, ..., a_N) of length N+1.
        N: truncation index; D_N kills a_{N-1} and a_N by the boundary rule.
    """
    poly = expand(sympify(poly))
    result = 0
    for n in range(N + 1):
        d_an = vars[n + 1] * vars[n + 2] if n + 2 <= N else 0
        if d_an != 0:
            result += poly.diff(vars[n]) * d_an
    return expand(result)


def verify_D(poly, vars, N):
    """Return True iff D_N(poly) == 0, else False."""
    return apply_D(poly, vars, N) == 0


def _fib(k):
    f0, f1 = 0, 1
    for _ in range(k):
        f0, f1 = f1, f0 + f1
    return f0


def _check(name, cond):
    print(("PASS" if cond else "FAIL") + " " + name)
    return cond


def main():
    from sympy import symbols

    ok = True
    # 1. Generator images and boundary rule, N general (spot values 2..6).
    for N in (2, 3, 4, 5, 6):
        a = symbols("a_0:%d" % (N + 1))
        ok &= _check("N=%d D(a_0)=a_1*a_2" % N, apply_D(a[0], a, N) == a[1] * a[2])
        ok &= _check("N=%d D(a_N)=0" % N, apply_D(a[N], a, N) == 0)
        ok &= _check("N=%d D(a_{N-1})=0" % N, apply_D(a[N - 1], a, N) == 0)
        ok &= _check("N=%d verify_D(a_N)" % N, verify_D(a[N], a, N) is True)
        ok &= _check("N=%d not verify_D(a_0)" % N, verify_D(a[0], a, N) is False)
        ok &= _check("N=%d verify_D(1)" % N, verify_D(1, a, N) is True)

    # 2. Leibniz rule spot check (N=4).
    N = 4
    a = symbols("a_0:%d" % (N + 1))
    f = a[0] ** 2 + 3 * a[1] * a[3]
    g = a[1] + a[2] ** 2
    ok &= _check(
        "N=4 Leibniz D(fg)=D(f)g+fD(g)",
        apply_D(f * g, a, N) == expand(apply_D(f, a, N) * g + f * apply_D(g, a, N)),
    )

    # 3. Nilpotency index on a_0 is the Fibonacci number tau_N = F_{N+1}.
    for N in (2, 3, 4, 5):
        a = symbols("a_0:%d" % (N + 1))
        tau = _fib(N + 1)
        orb = a[0]
        for _ in range(tau - 1):
            orb = apply_D(orb, a, N)
        ok &= _check(
            "N=%d D^(tau-1)(a_0)!=0 tau=F_%d=%d" % (N, N + 1, tau), orb != 0
        )
        ok &= _check(
            "N=%d D^tau(a_0)==0 tau=F_%d=%d" % (N, N + 1, tau),
            apply_D(orb, a, N) == 0,
        )

    print("harness OK" if ok else "harness FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
