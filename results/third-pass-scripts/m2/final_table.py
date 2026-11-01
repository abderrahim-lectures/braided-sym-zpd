import time
from build2 import M, T, alg_from_spanning
from build import product_of_fields
from alg import Alg

def blocks(p, s1, s2, A1, A2, Mlist):
    s=s1+s2; out=[]
    def emb(A, top):
        Mx=[[0]*s for _ in range(s)]
        for i in range(s1 if top else s2):
            for j in range(s1 if top else s2):
                Mx[i if top else s1+i][j if top else s1+j]=A[i][j]%p
        return Mx
    for A in A1: out.append(emb(A,True))
    for A in A2: out.append(emb(A,False))
    for B in Mlist: out.append(emb(B,True) if False else [[ (B[i][j] if (i<s1 and j>=s1) else 0) %p for j in range(s)] for i in range(s)])
    return out

def tri(p, A1m, A2m, Mm, name):
    s1=len(A1m[0]); s2=len(A2m[0]); s=s1+s2; mats=[]
    for A in A1m:
        Mx=[[0]*s for _ in range(s)]
        for i in range(s1):
            for j in range(s1): Mx[i][j]=A[i][j]%p
        mats.append(Mx)
    for A in A2m:
        Mx=[[0]*s for _ in range(s)]
        for i in range(s2):
            for j in range(s2): Mx[s1+i][s1+j]=A[i][j]%p
        mats.append(Mx)
    for B in Mm:
        Mx=[[0]*s for _ in range(s)]
        for i in range(s1):
            for j in range(s2): Mx[i][s1+j]=B[i][j]%p
        mats.append(Mx)
    return alg_from_spanning(p, mats, name)

def report(A):
    t0=time.time(); d1,d2=A.zpd_data(); D=A.derivations(); LD=A.local_derivations()
    print(f"{A.name:22s} p={A.p} n={A.n:2d} zpd={str(d1==d2):5s} ({d1:3d},{d2:3d}) dimDer={len(D):2d} dimLDer={len(LD):2d} {'LOCAL!=DER' if len(LD)>len(D) else 'equal':10s} [{time.time()-t0:.1f}s]", flush=True)

for p in (2,3,5):
    report(T(p,2)); report(T(p,3)) if p<5 else None
report(T(2,4))
for p in (2,3):
    report(M(p,2))
for p in (2,3,5):
    for m in (2,3,4): report(product_of_fields(p,m))
# Tri(K^2, K, K)
def tri_k2k(p):
    s=3
    dg=lambda a,b,c: [[a%p,0,0],[0,b%p,0],[0,0,c%p]]
    A1=[dg(1,1,1),dg(1,0,0),dg(0,1,0)]
    A2=[dg(1,1,1),dg(0,0,1)]
    Mm=[]
    for j in range(2):
        Mx=[[0]*3 for _ in range(3)]; Mx[j][2]=1; Mm.append(Mx)
    return tri(p,A1,A2,Mm,"Tri(K^2,K,K)(F%d)"%p)
def tri_m2k(p):
    s=3
    def blk(A,t):
        out=[[0]*s for _ in range(s)]
        for i in range(2):
            for j in range(2): out[i][j]=A[i][j]%p
        out[2][2]=t%p
        return out
    A1=[blk([[1,0],[0,1]],0),blk([[1,0],[0,0]],0),blk([[0,1],[0,0]],0),blk([[0,0],[1,0]],0),blk([[0,0],[0,1]],0)]
    A2=[blk([[1,0],[0,1]],1),blk([[0,0],[0,0]],1)]
    Mm=[]
    for i in range(2):
        Mx=[[0]*s for _ in range(s)]; Mx[i][2]=1; Mm.append(Mx)
    return tri(p,A1,A2,Mm,"Tri(M2,K,K)(F%d)"%p)
for p in (2,3,5):
    report(tri_k2k(p))
for p in (2,3):
    report(tri_m2k(p))
# products T_2 x K, T_2 x T_2, M_2(F_2) x K
def prod_blk(p, A1m, A2m, name):
    # block diagonal embeddings of two matrix algebras
    s1=len(A1m[0]); s2=len(A2m[0]); s=s1+s2; mats=[]
    for A in A1m:
        Mx=[[0]*s for _ in range(s)]
        for i in range(s1):
            for j in range(s1): Mx[i][j]=A[i][j]%p
        mats.append(Mx)
    for A in A2m:
        Mx=[[0]*s for _ in range(s)]
        for i in range(s2):
            for j in range(s2): Mx[s1+i][s1+j]=A[i][j]%p
        mats.append(Mx)
    return alg_from_spanning(p, mats, name)
t2=[[[1,0],[0,0]],[[0,1],[0,0]],[[0,0],[0,1]]]
k1=[[[1]]]
m2=[[[1,0],[0,0]],[[0,1],[0,0]],[[0,0],[1,0]],[[0,0],[0,1]]]
for p in (2,3,5):
    report(prod_blk(p,t2,k1,"T2 x K (F%d)"%p))
    report(prod_blk(p,t2,t2,"T2 x T2 (F%d)"%p))
for p in (2,3):
    report(prod_blk(p,m2,k1,"M2 x K (F%d)"%p))
