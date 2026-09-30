WT = (8,5,3,2,1,1); GW = (1,1,6,4,14,24,46)
P = {(0,0,0,0,1,0): QQ(1)}; Q = {(0,0,0,0,0,1): QQ(1)}
J1 = {(0,1,0,0,1,0): QQ(2),(0,0,2,0,0,0): QQ(-1)}
J2 = {(0,0,1,0,0,1): QQ(2),(0,0,0,2,0,0): QQ(-1)}
F0 = {(1,0,0,0,2,4):QQ(1),(0,1,1,1,1,3):QQ(-1),(0,1,0,3,1,2):QQ(1)/3,(0,0,2,3,0,2):QQ(1)/3,(0,0,1,5,0,1):QQ(-1)/5,(0,0,0,7,0,0):QQ(1)/35}
HMONO = [((11025),[2,0,0,0,4,4]),((-22050),[1,1,1,1,3,3]),((7350),[1,1,0,3,3,2]),((7350),[1,0,2,3,2,2]),((-4410),[1,0,1,5,2,1]),((630),[1,0,0,7,2,0]),((11025),[0,2,2,2,2,2]),((-7350),[0,2,1,4,2,1]),((1225),[0,2,0,6,2,0]),((6720),[0,1,5,0,1,3]),((-16800),[0,1,4,2,1,2]),((9450),[0,1,3,4,1,1]),((-1540),[0,1,2,6,1,0]),((-2208),[0,0,7,0,0,3]),((4368),[0,0,6,2,0,2]),((-2352),[0,0,5,4,0,1]),((385),[0,0,4,6,0,0])]
H = {tuple(e): QQ(c) for (c,e) in HMONO}
F46 = {}
with open('data/witness_w46.txt') as fh:
    for line in fh:
        sp = line.strip().split()
        F46[tuple(map(int,sp[0].split(',')))] = QQ(sp[1])
GENS = [P,Q,J1,J2,F0,H,F46]
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
def genmons(W):
    out = []
    def rec(i,rem,cur):
        if i == 6:
            if rem == 0: out.append(tuple(cur+[0]))
            elif rem == 46: out.append(tuple(cur+[1]))
            return
        for e in range(rem//GW[i]+1): rec(i+1,rem-e*GW[i],cur+[e])
    rec(0,W,[]); return out
def expge(ge):
    R = {(0,0,0,0,0,0): QQ(1)}
    for i,e in enumerate(ge):
        if e: R = pmul(R,ppow(GENS[i],e))
    return R
t = cputime()
F46sq = pmul(F46, F46)
print('F46^2 terms:', len(F46sq), 't=%.1fs' % (cputime()-t), flush=True)
# target space: C5_92 + F46*C5_46  == all 7-gen-monomials of wt 92 with F46-exp <= 1
cols = []
for ge in genmons(92):
    if ge[6] <= 1:
        cols.append(expge(ge))
print('ncols:', len(cols), flush=True)
rows = {}
for C in cols:
    for m in C:
        if m not in rows: rows[m] = len(rows)
# add target monomials to rows
for m in F46sq:
    if m not in rows: rows[m] = len(rows)
M = Matrix(QQ, len(rows), len(cols), sparse=True)
for j, C in enumerate(cols):
    for m, c in C.items(): M[rows[m], j] = c
t = cputime()
# solve M x = F46sq: augment and check consistency via rank comparison
r1 = M.rank()
Ma = Matrix(QQ, len(rows), len(cols)+1, sparse=True)
for j, C in enumerate(cols):
    for m, c in C.items(): Ma[rows[m], j] = c
for m, c in F46sq.items(): Ma[rows[m], len(cols)] = c
r2 = Ma.rank()
print('rank M =', r1, 'rank aug =', r2, 't=%.1fs' % (cputime()-t), flush=True)
print('F46^2 in C5_92 + F46*C5_46:', r1 == r2, flush=True)
