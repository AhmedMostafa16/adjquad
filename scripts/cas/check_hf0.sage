WT = (8,5,3,2,1,1)
P = {(0,0,0,0,1,0): QQ(1)}; Q = {(0,0,0,0,0,1): QQ(1)}
J1 = {(0,1,0,0,1,0): QQ(2),(0,0,2,0,0,0): QQ(-1)}
J2 = {(0,0,1,0,0,1): QQ(2),(0,0,0,2,0,0): QQ(-1)}
F0 = {(1,0,0,0,2,4):QQ(1),(0,1,1,1,1,3):QQ(-1),(0,1,0,3,1,2):QQ(1)/3,(0,0,2,3,0,2):QQ(1)/3,(0,0,1,5,0,1):QQ(-1)/5,(0,0,0,7,0,0):QQ(1)/35}
HMONO = [((11025),[2,0,0,0,4,4]),((-22050),[1,1,1,1,3,3]),((7350),[1,1,0,3,3,2]),((7350),[1,0,2,3,2,2]),((-4410),[1,0,1,5,2,1]),((630),[1,0,0,7,2,0]),((11025),[0,2,2,2,2,2]),((-7350),[0,2,1,4,2,1]),((1225),[0,2,0,6,2,0]),((6720),[0,1,5,0,1,3]),((-16800),[0,1,4,2,1,2]),((9450),[0,1,3,4,1,1]),((-1540),[0,1,2,6,1,0]),((-2208),[0,0,7,0,0,3]),((4368),[0,0,6,2,0,2]),((-2352),[0,0,5,4,0,1]),((385),[0,0,4,6,0,0])]
H = {tuple(e): QQ(c) for (c,e) in HMONO}
GENS6 = [P,Q,J1,J2,F0,H]
GW6 = (1,1,6,4,14,24)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def pmul(A,B):
    from collections import defaultdict
    R = defaultdict(int)
    for a,ca in A.items():
        for b,cb in B.items(): R[add(a,b)] += ca*cb
    return {k:v for k,v in R.items() if v != 0}
def ppow(A,n):
    R = {(0,0,0,0,0,0): QQ(1)}
    for _ in range(n): R = pmul(R,A)
    return R
def genmons6(W):
    out = []
    def rec(i,rem,cur):
        if i == 5:
            if rem % GW6[5] == 0: out.append(tuple(cur+[rem//GW6[5]]))
            return
        for e in range(rem//GW6[i]+1): rec(i+1,rem-e*GW6[i],cur+[e])
    rec(0,W,[]); return out
def expge6(ge):
    R = {(0,0,0,0,0,0): QQ(1)}
    for i,e in enumerate(ge):
        if e: R = pmul(R,ppow(GENS6[i],e))
    return R
def Kmon(w):
    out = []
    for c in range(w//6+1):
        for d in range((w-6*c)//4+1):
            r = w-6*c-4*d
            for a in range(r+1): out.append((a,r-a,c,d))
    return out
def Kexp(t):
    a,b,c,d = t
    R = {(0,0,0,0,0,0): QQ(1)}
    for _ in range(a): R = {(e[0],e[1],e[2],e[3],e[4]+1,e[5]):v for e,v in R.items()}
    for _ in range(b): R = {(e[0],e[1],e[2],e[3],e[4],e[5]+1):v for e,v in R.items()}
    J1E = {(0,1,0,0,1,0):QQ(2),(0,0,2,0,0,0):QQ(-1)}
    J2E = {(0,0,1,0,0,1):QQ(2),(0,0,0,2,0,0):QQ(-1)}
    for _ in range(c):
        N = {}
        for e,v in R.items():
            for t2,c2 in J1E.items():
                k = tuple(i+j for i,j in zip(e,t2)); N[k] = N.get(k,QQ(0))+v*c2
        R = N
    for _ in range(d):
        N = {}
        for e,v in R.items():
            for t2,c2 in J2E.items():
                k = tuple(i+j for i,j in zip(e,t2)); N[k] = N.get(k,QQ(0))+v*c2
        R = N
    return {k:v for k,v in R.items() if v != 0}
t = cputime()
T = pmul(H, F0)
print('target terms:', len(T), flush=True)
cols = []
# Block K: K_38 via Kmon/Kexp (monomials in p,q,J1,J2 only). NOTE: an earlier
# version used genmons6(38) here (= B_38, containing F0*H itself) making the
# test vacuous. This version tests the intended K-span.
for t_ in Kmon(38):
    cols.append(Kexp(t_))
F0E = expge6((0,0,0,0,1,0))
for t_ in Kmon(24):
    cols.append(pmul(F0E, Kexp(t_)))
HE = expge6((0,0,0,0,0,1))
for t_ in Kmon(14):
    cols.append(pmul(HE, Kexp(t_)))
# p^2 * B_36
for ge in genmons6(36):
    E = expge6(ge)
    C = {}
    for m, c in E.items():
        k = (m[0],m[1],m[2],m[3],m[4]+2,m[5])
        C[k] = C.get(k, QQ(0)) + c
    cols.append(C)
print('ncols:', len(cols), flush=True)
rows = {}
for C in cols:
    for m in C:
        if m not in rows: rows[m] = len(rows)
for m in T:
    if m not in rows: rows[m] = len(rows)
M = Matrix(QQ, len(rows), len(cols), sparse=True)
for j, C in enumerate(cols):
    for m, c in C.items(): M[rows[m], j] = c
r1 = M.rank()
Ma = Matrix(QQ, len(rows), len(cols)+1, sparse=True)
for j, C in enumerate(cols):
    for m, c in C.items(): Ma[rows[m], j] = c
for m, c in T.items(): Ma[rows[m], len(cols)] = c
r2 = Ma.rank()
print('rank =', r1, 'aug =', r2, 't=%.1fs' % (cputime()-t), flush=True)
print('HF0 in K+F0K+HK+p2B:', r1 == r2, flush=True)
