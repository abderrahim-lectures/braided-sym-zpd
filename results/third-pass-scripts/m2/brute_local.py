"""Brute-force count of local derivations (using the defining span condition) for small algebras."""
import itertools
from alg import Alg
from build2 import T, M
def brute_low(A):
    p,n,N=A.p,A.n,A.p**A.n
    els=list(A.elements()); idx={v:i for i,v in enumerate(els)}
    bi=[p**i for i in range(n)]
    add=lambda a,b: idx[tuple((els[a][q]+els[b][q])%p for q in range(n))]
    Ders=A.derivations()
    # image span of derivations at each element a: precompute the set of achievable values
    V={}
    for u in range(N):
        vecs=[tuple(A.apply(d,els[u])) for d in Ders]
        # all linear combinations
        s={tuple([0]*n)}
        for v in vecs:
            s = s | {tuple((a[q]+b[q])%p for q in range(n)) for a in s for b in [v]}
        V[u]=s
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
        if all(tuple(els[D[u]]) in V[u] for u in range(N)): cnt+=1
    dim=0; q=1
    while q<cnt: q*=A.p; dim+=1
    return cnt,dim
for A,label in [(T(2,2),"T_2(F_2)"),(T(3,2),"T_2(F_3)"),(M(2,2),"M_2(F_2)")]:
    c,d=brute_low(A)
    print(f"{label}: brute #local-der={c} (dim {d})  alg.py dimLDer={len(A.local_derivations())} dimDer={len(A.derivations())}", flush=True)
