import time
from build import from_mats
from alg import Alg

def blockdiag(p, b1, b2, name):
    s1=len(b1[0]); s2=len(b2[0]); s=s1+s2
    def emb(M, s1, s2, left):
        out=[[0]*s for _ in range(s)]
        for i in range(s1 if left else s2):
            for j in range(s1 if left else s2):
                out[i if left else s1+i][j if left else s1+j]=M[i][j]
        return out
    mats=[emb(b1[0],s1,s2,True)]  # identity of the product = I_{s1} + I_{s2}
    out=[[0]*s for _ in range(s)]
    for i in range(s): out[i][i]=1
    mats=[out]+[emb(M,s1,s2,True) for M in b1[1:]]+[emb(M,s1,s2,False) for M in b2[1:]]
    return from_mats(p, mats, name)

def t2units(p):
    d=[[1,0],[0,0]]; u=[[0,1],[0,0]]; e=[[1 if i==j else 0 for j in range(2)] for i in range(2)]
    return [e,d,u]

def report(A):
    t0=time.time(); d1,d2=A.zpd_data(); D=A.derivations(); LD=A.local_derivations()
    print(f"{A.name:20s} p={A.p} n={A.n:2d} zpd={d1==d2} ({d1},{d2}) dimDer={len(D):2d} dimLDer={len(LD):2d} {'EXTRA' if len(LD)>len(D) else 'equal'} [{time.time()-t0:.1f}s]", flush=True)

for p in (2,3,5):
    report(blockdiag(p, t2units(p), t2units(p), "T2 x T2 (F%d)"%p))
    report(blockdiag(p, t2units(p), [[[1]],], "T2 x K (F%d)"%p))
