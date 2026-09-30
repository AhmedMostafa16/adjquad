"""Relation hunt (discovery, mod 1000003): ker(7-gen map -> A_w) vs known (S,p2T-E).
For each weight w: M = gen-monomial expansions (p,q,J1,J2,F0,H,F46);
K = expansions of S*a and (p2T-E)*b (a,b 7-gen-monomials of complementary
weight). excess = nullity(M) - rank(K). excess>0 => NEW relation (extract next).
Run: sage scripts/cas/relation_hunt.sage (stdout log)
"""
ELL = 1000003
WT = (8, 5, 3, 2, 1, 1)
GW = (1, 1, 6, 4, 14, 24, 46)
P = {(0, 0, 0, 0, 1, 0): 1}
Q = {(0, 0, 0, 0, 0, 1): 1}
J1 = {(0, 1, 0, 0, 1, 0): 2, (0, 0, 2, 0, 0, 0): ELL - 1}
J2 = {(0, 0, 1, 0, 0, 1): 2, (0, 0, 0, 2, 0, 0): ELL - 1}
F0 = {(1, 0, 0, 0, 2, 4): 1, (0, 1, 1, 1, 1, 3): ELL - 1}
F0.update({(0, 1, 0, 3, 1, 2): pow(3, -1, ELL)})
F0.update({(0, 0, 2, 3, 0, 2): pow(3, -1, ELL)})
F0.update({(0, 0, 1, 5, 0, 1): ELL - pow(5, -1, ELL)})
F0.update({(0, 0, 0, 7, 0, 0): pow(35, -1, ELL)})
HMONO = [((11025), [2, 0, 0, 0, 4, 4]),
          ((-22050), [1, 1, 1, 1, 3, 3]),
          ((7350), [1, 1, 0, 3, 3, 2]),
          ((7350), [1, 0, 2, 3, 2, 2]),
          ((-4410), [1, 0, 1, 5, 2, 1]),
          ((630), [1, 0, 0, 7, 2, 0]),
          ((11025), [0, 2, 2, 2, 2, 2]),
          ((-7350), [0, 2, 1, 4, 2, 1]),
          ((1225), [0, 2, 0, 6, 2, 0]),
          ((6720), [0, 1, 5, 0, 1, 3]),
          ((-16800), [0, 1, 4, 2, 1, 2]),
          ((9450), [0, 1, 3, 4, 1, 1]),
          ((-1540), [0, 1, 2, 6, 1, 0]),
          ((-2208), [0, 0, 7, 0, 0, 3]),
          ((4368), [0, 0, 6, 2, 0, 2]),
          ((-2352), [0, 0, 5, 4, 0, 1]),
          ((385), [0, 0, 4, 6, 0, 0])]
H = {tuple(e): c % ELL for (c, e) in HMONO}
F46 = {}
with open('data/witness_w46.txt') as fh:
    for line in fh:
        sp = line.strip().split()
        F46[tuple(map(int, sp[0].split(',')))] = int(sp[1]) % ELL
GENS = [P, Q, J1, J2, F0, H, F46]


def add(e1, e2):
    return (e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2],
            e1[3] + e2[3], e1[4] + e2[4], e1[5] + e2[5])


def pmul(A, B):
    from collections import defaultdict
    R = defaultdict(int)
    for a, ca in A.items():
        for b, cb in B.items():
            R[add(a, b)] = (R[add(a, b)] + ca * cb) % ELL
    return dict(R)


def ppow(A, n):
    R = {(0, 0, 0, 0, 0, 0): 1}
    for _ in range(n):
        R = pmul(R, A)
    return R


def genmons(W):
    # 7 generators (p,q,J1,J2,F0,H,F46); F46^2 (wt 92) excluded in range.
    out = []

    def rec(i, rem, cur):
        if i == 6:
            if rem == 0:
                out.append(tuple(cur + [0]))
            elif rem == 46:
                out.append(tuple(cur + [1]))
            return
        for e in range(rem // GW[i] + 1):
            rec(i + 1, rem - e * GW[i], cur + [e])
    rec(0, W, [])
    return out


def expand_ge(ge):
    R = {(0, 0, 0, 0, 0, 0): 1}
    for i, e in enumerate(ge):
        if e:
            R = pmul(R, ppow(GENS[i], e))
    return R


# known relations as A-polys (mod ELL): S (wt28), p2T-E (wt48, T->F46)
# S = q^4*H - 11025*F0^2 - 105*q^2*J2^5*J1 - 9*J2^7
Sq = pmul(ppow(Q, 4), H)
Sq = {k: v for k, v in Sq.items()}
_t = pmul({(0, 0, 0, 0, 0, 0): (-11025) % ELL}, ppow(F0, 2))
for k, v in _t.items():
    Sq[k] = (Sq.get(k, 0) + v) % ELL
_t = pmul({(0, 0, 0, 0, 0, 0): (-105) % ELL},
          pmul(pmul(ppow(Q, 2), ppow(J2, 5)), J1))
for k, v in _t.items():
    Sq[k] = (Sq.get(k, 0) + v) % ELL
_t = pmul({(0, 0, 0, 0, 0, 0): (-9) % ELL}, ppow(J2, 7))
for k, v in _t.items():
    Sq[k] = (Sq.get(k, 0) + v) % ELL
Sq = {k: v for k, v in Sq.items() if v != 0}
# E = 40000q^6J1^7 + ... + H^2 ; p2T-E relation poly in A: p^2*F46 - E
p2F = pmul(ppow(P, 2), F46)
Epoly = {(0, 0, 0, 0, 0, 0): 0}
Epoly = pmul({(0, 0, 0, 0, 6, 0): 40000 % ELL}, ppow(J1, 7))
Epoly.update({k: (Epoly.get(k, 0) + v) % ELL for k, v in
              pmul({(0, 0, 0, 0, 4, 0): 193200 % ELL},
                   pmul(ppow(J1, 6), ppow(J2, 2))).items()})
Epoly.update({k: (Epoly.get(k, 0) + v) % ELL for k, v in
              pmul({(0, 0, 0, 0, 2, 0): 325164 % ELL},
                   pmul(ppow(J1, 5), ppow(J2, 4))).items()})
Epoly.update({k: (Epoly.get(k, 0) + v) % ELL for k, v in
              pmul({(0, 0, 0, 0, 0, 0): 148225 % ELL},
                   pmul(ppow(J1, 4), ppow(J2, 6))).items()})
Epoly.update({k: (Epoly.get(k, 0) + v) % ELL for k, v in
              pmul({(0, 0, 0, 0, 2, 0): 840 % ELL},
                   pmul(pmul(ppow(J1, 3), J2), H)).items()})
Epoly.update({k: (Epoly.get(k, 0) + v) % ELL for k, v in
              pmul({(0, 0, 0, 0, 0, 0): 770 % ELL},
                   pmul(pmul(ppow(J1, 2), ppow(J2, 3)), H)).items()})
Epoly.update({k: (Epoly.get(k, 0) + v) % ELL for k, v in
              pmul(H, H).items()})
Epoly = {k: v % ELL for k, v in Epoly.items() if v % ELL != 0}
REL = {k: (p2F.get(k, 0) - Epoly.get(k, 0)) % ELL
       for k in set(p2F) | set(Epoly)}
REL = {k: v for k, v in REL.items() if v != 0}
print("REL terms (p2F46-E, should be ~0):", len(REL), flush=True)


def amat(w, r, c, data):
    M = Matrix(GF(ELL), r, c, sparse=True)
    for (i, j, v) in data:
        M[i, j] = v
    return M


# formal known relations as 7-gen exponent tuples (mod ELL)
S_form = [((0, 4, 0, 0, 0, 1, 0), 1),
          ((0, 0, 0, 0, 2, 0, 0), (-11025) % ELL),
          ((0, 2, 1, 5, 0, 0, 0), (-105) % ELL),
          ((0, 0, 0, 7, 0, 0, 0), (-9) % ELL)]
R_form = [((2, 0, 0, 0, 0, 0, 1), 1),
          ((0, 6, 7, 0, 0, 0, 0), (-40000) % ELL),
          ((0, 4, 6, 2, 0, 0, 0), (-193200) % ELL),
          ((0, 2, 5, 4, 0, 0, 0), (-325164) % ELL),
          ((0, 0, 4, 6, 0, 0, 0), (-148225) % ELL),
          ((0, 2, 3, 1, 0, 1, 0), (-840) % ELL),
          ((0, 0, 2, 3, 0, 1, 0), (-770) % ELL),
          ((0, 0, 0, 0, 0, 2, 0), (ELL - 1))]
# sanity: formal relations vanish in A (spot-check S and R formal vs expansion)
_chkS = {}
for e, c in S_form:
    for m, v in expand_ge(e).items():
        _chkS[m] = (_chkS.get(m, 0) + c * v) % ELL
_chkS = {k: v for k, v in _chkS.items() if v != 0}
print("S formal vanishes in A:", len(_chkS) == 0, flush=True)
_chkR = {}
for e, c in R_form:
    for m, v in expand_ge(e).items():
        _chkR[m] = (_chkR.get(m, 0) + c * v) % ELL
_chkR = {k: v for k, v in _chkR.items() if v != 0}
print("R formal vanishes in A:", len(_chkR) == 0, flush=True)


def tadd(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3],
            a[4] + b[4], a[5] + b[5], a[6] + b[6])


for w in (46, 47, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 74, 80, 86, 92):
    t = cputime()
    gm = genmons(w)
    gidx = {g: j for j, g in enumerate(gm)}
    ex = [expand_ge(ge) for ge in gm]
    rows = {}
    for E in ex:
        for m in E:
            if m not in rows:
                rows[m] = len(rows)
    M = Matrix(GF(ELL), len(rows), len(gm), sparse=True)
    for j, E in enumerate(ex):
        for m, c in E.items():
            M[rows[m], j] = c
    nullM = len(gm) - M.rank()
    # known-generated subspace of k^genmons: S*a + R*b (formal products)
    kcols = []
    if w >= 28:
        for ge in genmons(w - 28):
            d = {}
            for e, c in S_form:
                k = tadd(e, ge)
                if k in gidx:
                    d[gidx[k]] = (d.get(gidx[k], 0) + c) % ELL
            kcols.append(d)
    if w >= 48:
        for ge in genmons(w - 48):
            d = {}
            for e, c in R_form:
                k = tadd(e, ge)
                if k in gidx:
                    d[gidx[k]] = (d.get(gidx[k], 0) + c) % ELL
            kcols.append(d)
    if kcols:
        K = Matrix(GF(ELL), len(gm), len(kcols), sparse=True)
        for j, d in enumerate(kcols):
            for i, c in d.items():
                K[i, j] = c
        rK = K.rank()
    else:
        rK = 0
    print(f"w={w} A={len(rows)} gen={len(gm)} null={nullM} known={rK} "
          f"excess={nullM - rK} t={cputime()-t:.1f}s", flush=True)
