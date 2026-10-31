"""Correct brute force: basis element e_i has ELEMENT index p^i."""
import itertools
from build2 import T, M
from alg import Alg
def brute(A):
    p,n,N = A.p, A.n, A.p**A.n
    els=list(A.elements()); idx={v:i for i,v in enumerate(els)}
    table=[[idx[A.prod(u,v)] for v in els] for u in els]
    bi=[p**i for i in range(n)]           # element index of the i-th basis vector
    add=lambda a,b: idx[tuple((els[a][q]+els[b][q])%p for q in range(n))]
    cnt=0; found=[]
    for code in itertools.product(range(N), repeat=n):
        D=[0]*N
        for u in range(N):
            co=els[u]; out=[0]*n
            for j in range(n):
                if co[j]:
                    im=els[code[j]]
                    for q in range(n): out[q]=(out[q]+co[j]*im[q])%p
            D[u]=idx[tuple(out)]
        ok=True
        for i in range(n):
            if not ok: break
            for j in range(n):
                if D[table[bi[i]][bi[j]]] != add(table[D[bi[i]]][bi[j]], table[bi[i]][D[bi[j]]]):
                    ok=False; break
        if ok: cnt+=1; found.append(code)
    dim=0; q=1
    while q<cnt: q*=A.p; dim+=1
    return cnt,dim,found

def kx3(p):
    n=3
    mult=[[[0]*n for _ in range(n)] for _ in range(n)]
    for j in range(n): mult[0][j]=[1 if k==j else 0 for k in range(n)]
    for i in range(n): mult[i][0]=[1 if k==i else 0 for k in range(n)]
    mult[1][1]=[0,0,1]
    return Alg(p,mult,one=0)
def dual(p):
    n=2
    mult=[[[0]*n for _ in range(n)] for _ in range(n)]
    mult[0][0]=[1,0]; mult[0][1]=[0,1]; mult[1][0]=[0,1]; mult[1][1]=[0,0]
    return Alg(p,mult,one=0)
for A,label in [(dual(3),"F_3[e]/e^2"),(dual(2),"F_2[e]/e^2"),(T(3,2),"T_2(F_3)"),(T(2,2),"T_2(F_2)"),
                (kx3(3),"F_3[x]/x^3"),(kx3(2),"F_2[x]/x^3")]:
    c,d,f=brute(A)
    print(f"{label:14s}: brute #der={c} (dim {d})   alg.py dim={len(A.derivations())}  {'AGREE' if d==len(A.derivations()) else 'DISAGREE'}", flush=True)
print("now M_2(F_2): 2^16 maps", flush=True)
A=M(2,2); c,d,f=brute(A)
print(f"M_2(F_2)      : brute #der={c} (dim {d})   alg.py dim={len(A.derivations())}  {'AGREE' if d==len(A.derivations()) else 'DISAGREE'}")
