"""Independent validation: for zpd algebras from the exhaustive enumeration, compare
dim Der from alg.py with a brute force over all linear maps.  Also confirm no extra
local derivations."""
import itertools, time
from alg import Alg
def brute_dim_der(A):
    p,n,N=A.p,A.n,A.p**A.n
    els=list(A.elements()); idx={v:i for i,v in enumerate(els)}
    table=[[idx[A.prod(u,v)] for v in els] for u in els]
    bi=[p**i for i in range(n)]
    add=lambda a,b: idx[tuple((els[a][q]+els[b][q])%p for q in range(n))]
    cnt=0
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
        if ok: cnt+=1
    return cnt
def load(path,p,n):
    for line in open(path):
        v=[int(x) for x in line.split()]
        yield Alg(p,[[[v[(i*n+j)*n+k] for k in range(n)] for j in range(n)] for i in range(n)],one=0)
t0=time.time(); checked=0; bad=0
for path,p,n,limit in [("algs_2_3.txt",2,3,100),("algs_3_3.txt",3,3,40)]:
    k=0
    for A in load(path,p,n):
        dk,dz=A.zpd_data()
        if dk!=dz: continue
        b=brute_dim_der(A); g=A.p**len(A.derivations())
        if b!=g: bad+=1; print("MISMATCH", path, b, g)
        LD=A.local_derivations()
        if len(LD)>len(A.derivations()): print("EXTRA local derivation in zpd algebra!", path)
        checked+=1; k+=1
        if k>=limit: break
print(f"cross-checked {checked} zpd algebras, mismatches {bad} [{time.time()-t0:.0f}s]")
