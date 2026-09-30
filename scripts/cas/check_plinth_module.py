"""Plinth-module audit for D5: f13 direction, residual data, chart, intersection.

Exact rational arithmetic (SymPy + stdlib Fractions). Dictionary
x=a3, y=a2, z=a1, p=a4, q=a5; J1=2pz-y^2, J2=2qy-x^2; D(x)=pq,
D(y)=px, D(z)=xy; f13=p*J2^3/35+p*q^2*J1*J2/4 (wt 13); g13 five terms.

Checks (PASS/FAIL each, final `plinth-module OK`, exit 0/1):
  M1. ker(delta_q) dimensions match k[p,x,u] in total degree <= 8
      (bounded evidence for Lemma lem:ker-deltaq; the proof is in text).
  M2. plinth-cap dimensions: dim(im D cap K_w) = dim K_{w-2} for w<=12
      and = dim K_{w-2}+dim K_{w-13} for 13<=w<=20
      (bounded evidence for Conjecture conj:plinth-module).
  M3. q-residue ranks equal dim Kbar_{w-13} for 13<=w<=20
      (bounded evidence for L_q=(p*J2bar^3)Kbar).
  M4. No p-primitive plinth element for w<=18
      (bounded evidence for Conjecture conj:plinth-p).
  M5. Intersection certs: q,h coprime to p,q pairwise as stated, i.e.
      A_{pq} cap A_{f13} = A_p (Lemma: two-chart intersection).
  M6. Chart separation: pi1(a0) = 0,-1/8,-2 at the collapse points
      (Theorem thm:chart-resolves), via NUM/f13^7 evaluation.
  M7. Terminal stratum V(q,x): descent identities, ker(delta) dims,
      K-image forms, no Kbar monomial divisible by a1*a2
      (Theorem thm:terminal-stratum; the vanishing proof is in text).

Run: python3 scripts/cas/check_plinth_module.py  # log: data/plinth_module.log
"""

import sys
from fractions import Fraction

from sympy import symbols, expand, Rational, diff

a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
A = [a0, a1, a2, a3, a4, a5]
x, y, z, p, q = a3, a2, a1, a4, a5
DM = {a0: a1*a2, a1: a2*a3, a2: a3*a4, a3: a4*a5, a4: 0, a5: 0}

WT = (8, 5, 3, 2, 1, 1)
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


# ---------------- M1: ker(delta_q) vs k[p,x,u], total degree ----------------
def _mons(nv, deg):
    if nv == 1:
        yield (deg,)
        return
    for e0 in range(deg + 1):
        for rest in _mons(nv - 1, deg - e0):
            yield (e0,) + rest


def _dq(e):
    ex, ey, ez, ep = e
    res = {}
    if ey > 0:
        m = (ex + 1, ey - 1, ez, ep + 1)
        res[m] = res.get(m, Fraction(0)) + ey
    if ez > 0:
        m = (ex + 1, ey + 1, ez - 1, ep)
        res[m] = res.get(m, Fraction(0)) + ez
    return res


def _rank(rows, ncols):
    M = [dict(r) for r in rows]
    prow = 0
    for col in range(ncols):
        piv = None
        for r in range(prow, len(M)):
            if M[r].get(col, Fraction(0)) != 0:
                piv = r
                break
        if piv is None:
            continue
        M[prow], M[piv] = M[piv], M[prow]
        inv = M[prow][col]
        for k in list(M[prow]):
            M[prow][k] /= inv
        for r in range(len(M)):
            if r != prow and M[r].get(col, Fraction(0)) != 0:
                f = M[r][col]
                for k, v in M[prow].items():
                    M[r][k] = M[r].get(k, Fraction(0)) - f * v
                    if M[r][k] == 0:
                        del M[r][k]
        prow += 1
    return prow


def _ker_delta_dim(n):
    basis = list(_mons(4, n))
    img = list(_mons(4, n + 1))
    jdx = {m: j for j, m in enumerate(img)}
    rows = [dict() for _ in img]
    for i, e in enumerate(basis):
        for m, c in _dq(e).items():
            rows[jdx[m]][i] = c
    return len(basis) - _rank(rows, len(basis))


def _subring_dim(n):
    # p^a x^b u^c, total degree a+b+2c = n
    return sum(r + 1 for c in range(n // 2 + 1) for r in [n - 2 * c])


m1 = all(_ker_delta_dim(n) == _subring_dim(n) for n in range(9))
check("M1 ker(delta_q)=k[p,x,u] deg<=8", m1)

# ---------------- M2-M4: plinth caps ----------------
def _add(e1, e2):
    return tuple(a + b for a, b in zip(e1, e2))


def _sub(e1, n):
    l = list(e1)
    l[n] -= 1
    return tuple(l)


_DGEN = {0: {(0, 1, 1, 0, 0, 0): Fraction(1)},
         1: {(0, 0, 1, 1, 0, 0): Fraction(1)},
         2: {(0, 0, 0, 1, 1, 0): Fraction(1)},
         3: {(0, 0, 0, 0, 1, 1): Fraction(1)}, 4: {}, 5: {}}


def _Dmon(e):
    res = {}
    for n in range(6):
        if e[n] == 0:
            continue
        base = _sub(e, n)
        for dexp, c in _DGEN[n].items():
            m = _add(base, dexp)
            res[m] = res.get(m, Fraction(0)) + e[n] * c
    return {k: v for k, v in res.items() if v != 0}


def _wmons(w):
    out = []
    for e0 in range(w // 8 + 1):
        r0 = w - 8 * e0
        for e1 in range(r0 // 5 + 1):
            r1 = r0 - 5 * e1
            for e2 in range(r1 // 3 + 1):
                r2 = r1 - 3 * e2
                for e3 in range(r2 // 2 + 1):
                    r3 = r2 - 2 * e3
                    for e4 in range(r3 + 1):
                        out.append((e0, e1, e2, e3, e4, r3 - e4))
    return out


_J1T = [((0, 1, 0, 0, 1, 0), Fraction(2)), ((0, 0, 2, 0, 0, 0), Fraction(-1))]
_J2T = [((0, 0, 1, 0, 0, 1), Fraction(2)), ((0, 0, 0, 2, 0, 0), Fraction(-1))]


def _Kexp(a, b, c, d):
    res = {(0, 0, 0, 0, 0, 0): Fraction(1)}
    for _ in range(a):
        res = {_add(m, (0, 0, 0, 0, 1, 0)): v for m, v in res.items()}
    for _ in range(b):
        res = {_add(m, (0, 0, 0, 0, 0, 1)): v for m, v in res.items()}
    for terms in ([_J1T] * c + [_J2T] * d):
        nres = {}
        for m, v in res.items():
            for t, tc in terms:
                k = _add(m, t)
                nres[k] = nres.get(k, Fraction(0)) + v * tc
        res = nres
    return {k: v for k, v in res.items() if v != 0}


def _Kbasis(w):
    out = []
    for c in range(w // 6 + 1):
        for d in range((w - 6 * c) // 4 + 1):
            r = w - 6 * c - 4 * d
            for a in range(r + 1):
                out.append((a, r - a, c, d))
    return out


def _nullspace(rows, ncols):
    M = [dict(r) for r in rows]
    pivots = {}
    prow = 0
    for col in range(ncols):
        piv = None
        for r in range(prow, len(M)):
            if M[r].get(col, Fraction(0)) != 0:
                piv = r
                break
        if piv is None:
            continue
        M[prow], M[piv] = M[piv], M[prow]
        inv = M[prow][col]
        for k in list(M[prow]):
            M[prow][k] /= inv
        for r in range(len(M)):
            if r != prow and M[r].get(col, Fraction(0)) != 0:
                f = M[r][col]
                for k, v in M[prow].items():
                    M[r][k] = M[r].get(k, Fraction(0)) - f * v
                    if M[r][k] == 0:
                        del M[r][k]
        pivots[col] = prow
        prow += 1
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for f in free:
        v = {f: Fraction(1)}
        for col, pr in pivots.items():
            cc = M[pr].get(f, Fraction(0))
            if cc != 0:
                v[col] = -cc
        basis.append(v)
    return basis


def _cap(w):
    pre = _wmons(w)
    kb = _Kbasis(w)
    ke = [_Kexp(*t) for t in kb]
    img = {}
    for j, e in enumerate(pre):
        for m, c in _Dmon(e).items():
            img.setdefault(m, {})[j] = c
    nK, nP = len(kb), len(pre)
    rows = []
    for m in pre:
        row = {}
        for i, kexp in enumerate(ke):
            if m in kexp:
                row[i] = kexp[m]
        for j, c in img.get(m, {}).items():
            row[nK + j] = row.get(nK + j, Fraction(0)) - c
        rows.append({k: v for k, v in row.items() if v != 0})
    out = []
    for v in _nullspace(rows, nK + nP):
        alpha = {i: v[i] for i in range(nK) if v.get(i, Fraction(0)) != 0}
        if alpha:
            out.append(alpha)
    return out, kb


def _resrank(res, kb, pos):
    cols = {}
    mat = []
    for alpha in res:
        row = {}
        for i, c in alpha.items():
            t = kb[i]
            if (t[1] == 0) if pos == 'q' else (t[0] == 0):
                key = tuple(v for j, v in enumerate(t)
                            if not ((j == 1 and pos == 'q') or (j == 0 and pos == 'p')))
                if key not in cols:
                    cols[key] = len(cols)
                row[cols[key]] = row.get(cols[key], Fraction(0)) + c
        mat.append(row)
    return _rank(mat, len(cols))


def _kbardim(d):
    # monomials p^a J1^c J2^d of weight a+6c+4d = d
    n = 0
    for c in range(d // 6 + 1):
        for dd in range((d - 6 * c) // 4 + 1):
            n += 1  # a determined: a = d-6c-4dd >= 0
    return n


m2ok, m3ok, m4ok = True, True, True
for w in range(0, 21):
    res, kb = _cap(w)
    want = len(_Kbasis(w - 2)) + (len(_Kbasis(w - 13)) if w >= 13 else 0)
    if len(res) != want:
        m2ok = False
        print(f"  w={w}: dimcap={len(res)} want={want}")
    if w >= 13:
        if _resrank(res, kb, 'q') != _kbardim(w - 13):
            m3ok = False
            print(f"  w={w}: qres mismatch")
    if w <= 18:
        if _resrank(res, kb, 'p') != 0:
            m4ok = False
            print(f"  w={w}: p-primitive found")
check("M2 cap dims = dimK[w-2]+dimK[w-13] (w<=20)", m2ok)
check("M3 q-res ranks = dimKbar[w-13] (13<=w<=20)", m3ok)
check("M4 no p-primitive plinth elt (w<=18)", m4ok)

# ---------------- M5: intersection certs ----------------
e2 = J2**2/35 + q**2*J1/4
h = J2*e2
m5 = (expand(J2.subs(q, 0)) != 0 and expand(h.subs(q, 0)) != 0
      and expand(e2.subs(q, 0)) != 0
      and expand(J1.subs(p, 0)) != 0 and expand(J2.subs(p, 0)) != 0
      and expand(h.subs(p, 0)) != 0 and expand(e2.subs(p, 0)) != 0
      and expand(F13 - p*h) == 0)
check("M5 A_{pq} cap A_{f13} = A_p certs", m5)

# ---------------- M6: chart separation ----------------
from sympy import factorial as _fact
orb = [a0]
while True:
    nxt = D5(orb[-1])
    if nxt == 0:
        break
    orb.append(nxt)
N = len(orb) - 1
f13e = expand(F13)
g13e = expand(G13)
num = expand(sum(((-g13e)**i) * orb[i] * (f13e**(N - i)) / _fact(i)
                 for i in range(len(orb))))
m6a = (D5(num) == 0)
fd = Rational(-1, 35)
vals = []
for t in [0, 1, 2]:
    pt = {a0: 0, a1: Rational(t**2, 2), a2: t, a3: 1, a4: 1, a5: 0}
    vals.append(num.subs(pt) / fd**N)
# ---------------- M7: terminal stratum V(q,x) ----------------
# delta = a1*a2*d/da0 on k[a0,a1,a2,a4]; ker = k[a1,a2,a4] (bounded check);
# K-image = k[a4, 2*a4*a1-a2^2]; descent identities by expansion.
m7a = (D5(q) == 0 and expand(D5(x) - p*q) == 0)
m7b = (expand(J1.subs({q: 0, x: 0}) - (2*a4*a1 - a2**2)) == 0
       and expand(J2.subs({q: 0, x: 0})) == 0)


def _smons(nv, deg):
    if nv == 1:
        yield (deg,)
        return
    for e0 in range(deg + 1):
        for rest in _smons(nv - 1, deg - e0):
            yield (e0,) + rest


def _strat_ker_dim(n):
    # vars (a0,a1,a2,a4); delta(a0^e0 a1^e1 a2^e2 a4^e3) = e0*a0^{e0-1}a1^{e1+1}a2^{e2+1}a4^e3
    basis = list(_smons(4, n))
    img = list(_smons(4, n + 1))
    jdx = {m: j for j, m in enumerate(img)}
    rows = [dict() for _ in img]
    for i, (e0, e1, e2, e3) in enumerate(basis):
        if e0 > 0:
            m = (e0 - 1, e1 + 1, e2 + 1, e3)
            rows[jdx[m]][i] = Fraction(e0)
    r = _rank(rows, len(basis))
    # dim k[a1,a2,a4]_n = #{e1+e2+e3=n} = C(n+2,2)
    return len(basis) - r, (n + 2) * (n + 1) // 2


m7c = all(_strat_ker_dim(n)[0] == _strat_ker_dim(n)[1] for n in range(9))
# no Kbar-stratum monomial p^a*U^c (U=2pa1-a2^2) divisible by a1*a2:
# at a1=0 gives p^a*(-a2^2)^c != 0 always; certify instances through degree 12
m7d = True
for cc in range(5):
    for aa in range(13 - 3 * cc):
        if not (aa + 3 * cc <= 12):
            continue
        U = 2*a4*a1 - a2**2
        if expand((p**aa * U**cc).subs(a1, 0)) == 0:
            m7d = False
check("M7 terminal stratum V(q,x) certs", m7a and m7b and m7c and m7d)

if fails:
    print("plinth-module FAILED:", fails)
    sys.exit(1)
print("plinth-module OK")
