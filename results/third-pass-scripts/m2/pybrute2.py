import itertools
from build2 import T, M
from alg import Alg
def brute(A, verbose=False):
    p,n,N = A.p, A.n, A.p**A.n
    els = list(A.elements()); idx = {v:i for i,v in enumerate(els)}
    table = [[idx[A.prod(u,v)] for v in els] for u in els]
    add = lambda a,b: idx[tuple((els[a][q]+els[b][q])%p for q in range(n))]
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
                if D[table[i][j]] != add(table[D[i]][j], table[i][D[j]]):
                    ok=False; break
        if ok: cnt+=1; found.append(code)
    return cnt, found

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
for A,label in [(dual(3),"F_3[e]/e^2"),(T(3,2),"T_2(F_3)"),(kx3(3),"F_3[x]/x^3"),(T(2,2),"T_2(F_2)"),(M(2,2),"M_2(F_2)?(dim4: skip)")]:
    if A.n>3 and A.n>4: continue
    if A.n==4 and A.p==2:
        print(label, "n=4: 2^16 maps, running...", flush=True)
    c,f = brute(A)
    dim=0; q=1
    while q<c: q*=A.p; dim+=1
    print(f"{label}: brute #der={c} = {A.p}^{dim}; alg.py dim={len(A.derivations())}", flush=True)
