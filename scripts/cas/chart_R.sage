"""Chart membership: pi1(b) in R_{f13}? For b in {a3,a2,a1,a0}:
solve NUM_b = (sum_j a_j M_j) * f13^s with M_j R-gen-monomials
(p,q,J1,J2,F0,H,F46 as weights allow), s from N_b-1 down.
Exact QQ sparse solve. First success per b = certificate.
Run: sage scripts/cas/chart_R.sage (stdout log)
"""
R = PolynomialRing(QQ, 'a0,a1,a2,a3,a4,a5')
a0, a1, a2, a3, a4, a5 = R.gens()
A = [a0, a1, a2, a3, a4, a5]
x, y, z, p, q = a3, a2, a1, a4, a5
Dmap = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}

J1 = 2*p*z - y**2
J2 = 2*q*y - x**2
F13 = p*J2**3/35 + p*q**2*J1*J2/4
G13 = (a0*p**2*q**3 - a1*a3**3*p*q/6 - 19*a2**3*a3*q**2/70
       + 101*a2**2*a3**3*q/420 - a2*a3**5/35)
F0 = (p**2*q**4*a0 - p*q**3*x*y*z + p*q**2*x**3*z/3
      + q**2*x**3*y**2/3 - q*x**5*y/5 + x**7/35)
H = (11025*a0**2*a4**4*a5**4 - 22050*a0*a1*a2*a3*a4**3*a5**3
     + 7350*a0*a1*a3**3*a4**3*a5**2 + 7350*a0*a2**2*a3**3*a4**2*a5**2
     - 4410*a0*a2*a3**5*a4**2*a5 + 630*a0*a3**7*a4**2
     + 11025*a1**2*a2**2*a3**2*a4**2*a5**2
     - 7350*a1**2*a2*a3**4*a4**2*a5 + 1225*a1**2*a3**6*a4**2
     + 6720*a1*a2**5*a4*a5**3 - 16800*a1*a2**4*a3**2*a4*a5**2
     + 9450*a1*a2**3*a3**4*a4*a5 - 1540*a1*a2**2*a3**6*a4
     - 2208*a2**7*a5**3 + 4368*a2**6*a3**2*a5**2
     - 2352*a2**5*a3**4*a5 + 385*a2**4*a3**6)
F46 = R(0)
with open('data/witness_w46.txt') as fh:
    for line in fh:
        sp = line.strip().split()
        e = tuple(map(int, sp[0].split(',')))
        F46 += QQ(sp[1]) * prod(v**i for v, i in zip(A, e))
GW = (1, 1, 6, 4, 14, 24, 46)
GENS = [p, q, J1, J2, F0, H, F46]


def D5(f):
    return sum(f.derivative(v) * Dmap[v] for v in A)


def genmons(W):
    # 7 generators (p,q,J1,J2,F0,H,F46); F46^2 (wt 92) included iff needed.
    out = []

    def rec(i, rem, cur):
        if i == 6:
            for e6 in range(rem // 46 + 1):
                if rem - 46 * e6 == 0:
                    out.append(tuple(cur + [e6]))
            return
        for e in range(rem // GW[i] + 1):
            rec(i + 1, rem - e * GW[i], cur + [e])
    rec(0, W, [])
    return out


def test_b(b, N, Nsols):
    orb = [R(b)]
    while True:
        nxt = D5(orb[-1])
        if nxt == 0:
            break
        orb.append(nxt)
    assert len(orb) - 1 == N
    from math import factorial
    NUM = sum(((-G13)**i) * orb[i] * (F13**(N - i)) / factorial(i)
              for i in range(len(orb)))
    for s in range(N - 1, -1, -1):
        Wg = None
        # weight of NUM:
        W = max(sum(e[i] * w for i, w in enumerate((8, 5, 3, 2, 1, 1)))
                for e in NUM.exponents())
        cols = []
        mons = []
        for ge in genmons(W - 13 * s):
            m = prod(g**e for g, e in zip(GENS, ge))
            cols.append((m * F13**s).dict())
        if not cols:
            continue
        rows = sorted(set().union(*[set(c) for c in cols]) | set(NUM.dict()))
        ri = {m: i for i, m in enumerate(rows)}
        M = Matrix(QQ, len(rows), len(cols), sparse=True)
        for j, C in enumerate(cols):
            for m, c in C.items():
                M[ri[m], j] = c
        t = vector(QQ, [NUM.dict().get(m, 0) for m in rows])
        try:
            sol = M.solve_right(t)
        except Exception:
            continue
        nz = [(j, sol[j]) for j in range(len(cols)) if sol[j] != 0]
        print(f"  pi1({b}): s={s} SUCCESS terms={len(nz)}", flush=True)
        for j, c in nz[:12]:
            print(f"    {c} * {genmons(W - 13*s)[j]}", flush=True)
        return True
    print(f"  pi1({b}): FAILED all s", flush=True)
    return False


print("chart membership pi1(b) in R_f13:", flush=True)
ok = True
ok &= test_b(a3, 1, None)
ok &= test_b(a2, 2, None)
ok &= test_b(a1, 4, None)
ok &= test_b(a0, 7, None)
print("ALL:", ok, flush=True)
