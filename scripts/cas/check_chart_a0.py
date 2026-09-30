"""a0-chart obstructions (exact): J2 |/- NUM_a0 kills s>=1; s=7,6 fail exactly.
With N=7 (pi1(a0) = NUM/f13^7): NUM = G*f13^s with s>=1 needs J2 | NUM;
NUM is nonzero (exact integers) at J2=0 points, so s>=1 impossible.
s=7 (G in K_8) and s=6 (G in R_21 = K_21+F0*K_7, complete) fail by exact
solve. Remaining: s=0 (NUM in R_99; see chart_R.sage, running) and t>=1.
Prints PASS/FAIL plus `chart-a0 OK` (exit 0/1).
Run: python3 scripts/cas/check_chart_a0.py  # log: data/chart_a0.log
"""
import sys
from fractions import Fraction
from sympy import symbols, expand, Rational, diff, factorial, Poly  # noqa: E402

a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
A = [a0, a1, a2, a3, a4, a5]
x, y, z, p, q = a3, a2, a1, a4, a5
DM = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}
J1 = 2*p*z - y**2
J2 = 2*q*y - x**2
F13 = Rational(1, 35)*p*J2**3 + Rational(1, 4)*p*q**2*J1*J2
G13 = (a0*p**2*q**3 - Rational(1, 6)*a1*a3**3*p*q
       - Rational(19, 70)*a2**3*a3*q**2 + Rational(101, 420)*a2**2*a3**3*q
       - Rational(1, 35)*a2*a3**5)

fails = []


def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name +
          ((" [" + str(detail) + "]") if detail else ""))
    if not cond:
        fails.append(name)


def D5(f):
    return expand(sum(diff(f, v) * DM[v] for v in A))


orb = [a0]
while True:
    nxt = D5(orb[-1])
    if expand(nxt) == 0:
        break
    orb.append(nxt)
N = len(orb) - 1
NUM = sum(((-G13)**i) * orb[i] * (F13**(N - i)) / factorial(i)
          for i in range(len(orb)))
check("D-orbit length N=7", N == 7, N)

# J2-obstruction: NUM nonzero at J2=0 points (exact integers)
pts = [{a0: 1, a1: 1, a2: 2, a3: 2, a4: 1, a5: 1},
       {a0: 2, a1: 3, a2: 4, a3: 4, a4: 2, a5: 2}]
vals = []
for pt in pts:
    assert expand(J2.subs(pt)) == 0
    vals.append(expand(NUM).subs(pt))
check("J2 |/- NUM (s>=1 impossible)", all(v != 0 for v in vals),
      [str(v)[:24] + "..." for v in vals])


def to_exp(poly):
    P = Poly(expand(poly), A)
    return {tuple(e): Fraction(c.p, c.q) for e, c in P.as_dict().items()}


NUME = to_exp(NUM)
F13E = to_exp(F13)


def Kexp(a, b, c, d):
    R = {(0, 0, 0, 0, 0, 0): Fraction(1)}
    for _ in range(a):
        R = {(e[0], e[1], e[2], e[3], e[4] + 1, e[5]): v for e, v in R.items()}
    for _ in range(b):
        R = {(e[0], e[1], e[2], e[3], e[4], e[5] + 1): v for e, v in R.items()}
    J1E = {(0, 1, 0, 0, 1, 0): Fraction(2), (0, 0, 2, 0, 0, 0): Fraction(-1)}
    J2E = {(0, 0, 1, 0, 0, 1): Fraction(2), (0, 0, 0, 2, 0, 0): Fraction(-1)}
    for _ in range(c):
        NN = {}
        for e, v in R.items():
            for t2, c2 in J1E.items():
                k = tuple(i + j for i, j in zip(e, t2))
                NN[k] = NN.get(k, Fraction(0)) + v * c2
        R = NN
    for _ in range(d):
        NN = {}
        for e, v in R.items():
            for t2, c2 in J2E.items():
                k = tuple(i + j for i, j in zip(e, t2))
                NN[k] = NN.get(k, Fraction(0)) + v * c2
        R = NN
    return {k: v for k, v in R.items() if v != 0}


def Kmon(w):
    out = []
    for c in range(w // 6 + 1):
        for d in range((w - 6 * c) // 4 + 1):
            r = w - 6 * c - 4 * d
            for a in range(r + 1):
                out.append((a, r - a, c, d))
    return out


def pmulE(X, Y):
    R = {}
    for a, ca in X.items():
        for b, cb in Y.items():
            k = tuple(i + j for i, j in zip(a, b))
            R[k] = R.get(k, Fraction(0)) + ca * cb
    return {k: v for k, v in R.items() if v != 0}


F0E = to_exp(p**2*q**4*a0 - p*q**3*x*y*z + Rational(1, 3)*p*q**2*x**3*z
             + Rational(1, 3)*q**2*x**3*y**2 - Rational(1, 5)*q*x**5*y
             + Rational(1, 35)*x**7)


def solve_test(cols, target):
    rows = sorted(set(target) | {m for C in cols for m in C})
    ri = {m: i for i, m in enumerate(rows)}
    M = [dict() for _ in rows]
    for j, C in enumerate(cols):
        for m, c in C.items():
            M[ri[m]][j] = c
    b = [target.get(m, Fraction(0)) for m in rows]
    piv = {}
    pr = 0
    for col in range(len(cols)):
        p = None
        for r in range(pr, len(M)):
            if M[r].get(col, Fraction(0)) != 0:
                p = r
                break
        if p is None:
            continue
        M[pr], M[p] = M[p], M[pr]
        b[pr], b[p] = b[p], b[pr]
        inv = M[pr][col]
        for k in list(M[pr]):
            M[pr][k] /= inv
        b[pr] /= inv
        for r in range(len(M)):
            if r != pr and M[r].get(col, Fraction(0)) != 0:
                f = M[r][col]
                for k, v in M[pr].items():
                    M[r][k] = M[r].get(k, Fraction(0)) - f * v
                    if M[r][k] == 0:
                        del M[r][k]
                b[r] -= f * b[pr]
        piv[col] = pr
        pr += 1
    return all(bool(M[r]) or b[r] == 0 for r in range(len(M)))


def f13pow(s):
    FS = {(0, 0, 0, 0, 0, 0): Fraction(1)}
    for _ in range(s):
        N2 = {}
        for e, v in FS.items():
            for t2, c2 in F13E.items():
                k = tuple(i + j for i, j in zip(e, t2))
                N2[k] = N2.get(k, Fraction(0)) + v * c2
        FS = N2
    return FS


# s=7: G in K_8
FS7 = f13pow(7)
cols7 = []
for t in Kmon(8):
    C = pmulE(Kexp(*t), FS7)
    cols7.append(C)
check("s=7 (global) fails", not solve_test(cols7, NUME))
# s=6: G in R_21 = K_21 + F0*K_7 (complete: no H/F46 below wt 24/46)
FS6 = f13pow(6)
cols6 = []
for t in Kmon(21):
    cols6.append(pmulE(Kexp(*t), FS6))
for t in Kmon(7):
    cols6.append(pmulE(pmulE(Kexp(*t), F0E), FS6))
check("s=6 fails (complete system)", not solve_test(cols6, NUME))

if fails:
    print("chart-a0 FAILED:", fails)
    sys.exit(1)
print("chart-a0 OK")
