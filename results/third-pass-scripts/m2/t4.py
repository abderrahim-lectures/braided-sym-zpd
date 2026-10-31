"""Tri(A1,M,A2) examples: block upper triangular matrices [[a1,m],[0,a2]]."""
import time
from build import from_mats, product_of_fields, full_matrix_units
from alg import Alg

def tri_mats(p, A1, A2, M):
    """A1,A2: lists of square matrices (basis, first = identity), M: list of matrices
    of shape len x len (all rows, cols) giving the bimodule. Embed in block matrices."""
    s1=len(A1[0]); s2=len(A2[0]); sm=len(M[0]); assert sm==s1 and len(M[0])==s2
    s=s1+s2
    def emb(A=None, Mm=None):
        out=[[0]*s for _ in range(s)]
        if A is not None:
            for i in range(s1):
                for j in range(s1): out[i][j]=A[i][j]%p
            for i in range(s2):
                for j in range(s2): out[s1+i][s1+j]=A2_id(i,j)
        return out
    # simpler: build explicitly
    mats=[]
    # unit of Tri = diag(1_{A1}, 1_{A2})
    I=[[0]*s for _ in range(s)]
    for i in range(s): I[i][i]=1
    mats.append(I)
    for A in A1[1:]:
        Mx=[[0]*s for _ in range(s)]
        for i in range(s1):
            for j in range(s1): Mx[i][j]=A[i][j]%p
        mats.append(Mx)
    for A in A2[1:]:
        Mx=[[0]*s for _ in range(s)]
        for i in range(s2):
            for j in range(s2): Mx[s1+i][s1+j]=A[i][j]%p
        mats.append(Mx)
    for B in M:
        if all(x==0 for row in B for x in row): continue
        Mx=[[0]*s for _ in range(s)]
        for i in range(s1):
            for j in range(s2): Mx[i][s1+j]=B[i][j]%p
        mats.append(Mx)
    return mats

def A2_id(i,j):
    return 0

def report(A):
    t0=time.time(); d1,d2=A.zpd_data(); D=A.derivations(); LD=A.local_derivations()
    print(f"{A.name:28s} p={A.p} n={A.n:2d} zpd={d1==d2} ({d1},{d2}) dimDer={len(D):2d} dimLDer={len(LD):2d} {'EXTRA' if len(LD)>len(D) else 'equal'} [{time.time()-t0:.1f}s]", flush=True)

def Kmat(p, v):  # 1x1 matrix
    return [[v%p]]

for p in (2,3,5):
    A1 = [Kmat(p,1)] + ([] if p==2 else [])   # K = A1 with basis 1 only
    # Tri(K, K, K) is T_2 -- already done, but include a 2-dim M:
    # Tri(K, K^2, K): s1=1, s2=1, M = 1x1 entries but we need two basis elements of M
    # build directly as matrices with two nilpotent positions? Use Tri(K^2, K, K) instead:
    pass

# Tri(K^2, K, K): A1 = K^2 as diagonal 2x2, A2 = K (1x1), M = row (1x2)
def tri_k2_k_k(p, name):
    s=3
    def dg(a,b,c):
        return [[a%p,0,0],[0,b%p,0],[0,0,c%p]]
    mats=[dg(1,1,1), dg(1,0,0), dg(0,1,0), dg(0,0,1)]
    for j in range(2):
        M=[[0]*3 for _ in range(3)]; M[j][2]=1; mats.append(M)
    return from_mats(p,mats,name)

for p in (2,3,5):
    report(tri_k2_k_k(p,"Tri(K^2,K,K) F%d"%p))

# Tri(M_2(F_2), K, K): s1=2, s2=1, M = column (2x1)
def tri_m2_k(p, name):
    s=3
    def blk(A, t):
        out=[[0]*s for _ in range(s)]
        for i in range(2):
            for j in range(2): out[i][j]=A[i][j]%p
        out[2][2]=t%p
        return out
    I2=[[1,0],[0,1]]; E=[[1,0],[0,0]]
    mats=[blk(I2,1), blk(E,0), blk([[0,1],[0,0]],0), blk([[0,0],[1,0]],0), blk([[0,0],[0,1]],0), blk([[0,0],[0,0]],1)]
    for i in range(2):
        M=[[0]*s for _ in range(s)]; M[i][2]=1; mats.append(M)
    return from_mats(p,mats,name)
report(tri_m2_k(2,"Tri(M2(F2),K,K)"))
report(tri_m2_k(3,"Tri(M2(F3),K,K)"))
