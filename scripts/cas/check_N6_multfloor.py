"""Multiplicity-floor certificate for N=6 saturation (a6-side, exact).

For fixed W#-degree m, the joint initial-form system from ALL of {C_k}
is P(r) = P'(r) = ... = P^{(K)}(r) = 0 with P(T) = sum_{j in S} h_j T^j
(the C_k equation is the k-th formal derivative of the C_0 equation).
So r must be a root of multiplicity >= K+1; with minpoly(r) of degree
d_r (char 0, separable), (K+1)*d_r <= m, i.e. the deficit lambda can
never be driven to >= 0 by initial forms alone: floor lambda >= -e*m.
The bound is sharp: minpoly-powers realize every deficit in the range.

Here on the a6-side (e_6 = 4): r_6 = a4^7/(35a5^2) = alpha*sbar with
alpha = -z4^3/(35z1), sbar = a4/a5, sbar^2 = -z4/z1^2 in L_6, so
m(T) = T^2 + alpha^2*z4/z1^2 is the (degree-2) minpoly with SIMPLE
root r_6. For deficit lambda = -4s, P_s = m(T)^s has exact multiplicity
s, satisfying the joint system at W#-degree 2s (e.g. s=1, m=2: the
H-shaped direction realized at N=5 by H itself, cf. check_s6.py
kill-shot; H sits exactly on the floor lambda >= -2m). The a5-side
follows the same pattern over its degree-<=4 tower (witnesses in
check_N6_sat.py).

Run:
    python3 scripts/cas/check_N6_multfloor.py  # log: data/n6/multfloor.log
Prints PASS/FAIL per check plus a final `check_N6_multfloor OK` (exit 0/1).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sympy import symbols, expand, cancel, diff  # noqa: E402

a4, a5, z1, z4, T = symbols("a4 a5 z1 z4 T")

R6 = a4**7/(35*a5**2)
ALPHA = -z4**3/(35*z1)
MINPOLY = T**2 + ALPHA**2*z4/z1**2
SIGMA = {z1: a5, z4: -a4**2}


def _ev(expr):
    """Evaluate at T = r_6 then specialize (exact rational cancellation)."""
    return cancel(expand(expr.subs(T, R6)).subs(SIGMA))


def minpoly_eval_zero():
    """m(r_6) = 0."""
    return _ev(MINPOLY) == 0


def minpoly_simple():
    """m'(r_6) = 2r_6 != 0 (root is simple; minpoly degree exactly 2)."""
    return _ev(diff(MINPOLY, T)) != 0


def mult_system(s):
    """(P = m^s, exact multiplicity s; joint system through k < s)."""
    P = expand(MINPOLY**s)
    ok_k = all(_ev(diff(P, T, k)) == 0 for k in range(s))
    exact = (_ev(diff(P, T, s - 1)) == 0 and _ev(diff(P, T, s)) != 0)
    return (2*s, ok_k, exact)


log = []


def check(name, cond):
    log.append(("PASS " if cond else "FAIL ") + name)
    return bool(cond)


def main():
    ok = True
    ok &= check("minpoly m(r_6) = 0", minpoly_eval_zero())
    ok &= check("minpoly simple root", minpoly_simple())
    for s in range(1, 7):
        deg, ok_k, exact = mult_system(s)
        log.append("  deficit -4*%d: P = m^%d (deg %d) kills k<%d, exact mult"
                   % (s, s, deg, s))
        ok &= check("s=%d joint system P^(k)(r6)=0 for k<%d" % (s, s), ok_k)
        ok &= check("s=%d exact multiplicity %d" % (s, deg), exact)
    for ln in log:
        print(ln)
    print("check_N6_multfloor OK" if ok else "check_N6_multfloor FAILED")
    try:
        os.makedirs("data/n6", exist_ok=True)
        with open("data/n6/multfloor.log", "w") as fh:
            fh.write("\n".join(
                log + ["check_N6_multfloor OK" if ok
                       else "check_N6_multfloor FAILED"]) + "\n")
    except Exception as exc:  # pragma: no cover
        print("log-write:", exc)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
