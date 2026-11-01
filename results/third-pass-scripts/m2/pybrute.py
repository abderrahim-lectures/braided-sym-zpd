"""Dead-simple Python brute force over all linear maps for small algebras."""
import itertools
from build2 import T
from alg import Alg
def brute(A):
    p,n,N = A.p, A.n, A.p**A.n
    els = list(A.elements())
    idx = {v:i for i,v in enumerate(els)}
    table = [[idx[A.prod(u,v)] for v in els] for u in els]
    basis = [A.unit(i) for i in range(n)]
    cnt = 0; found=[]
    for code in itertools.product(range(N), repeat=n):
        # D(e_j) = els[code[j]]
        D = [None]*N
        for u in range(N):
            coords = els[u]; out=[0]*n
            for j in range(n):
                cj = coords[j]
                if cj:
                    im = els[code[j]]
                    for q in range(n): out[q] = (out[q] + cj*im[q]) % p
            D[u] = idx[tuple(out)]
        ok=True
        for i in range(n):
            for j in range(n):
                if D[table[i][j]] != table[D[i]][j] and True:
                    t1 = table[D[i]][j]; t2 = table[i][D[j]]
                    # add elements t1+t2
                    s = tuple((els[t1][q]+els[t2][q])%p for q in range(n))
                    if D[table[i][j]] != idx[s]:
                        ok=False; break
            if not ok: break
        if ok:
            cnt+=1; found.append(code)
    return cnt, found

def kx3(p):
    n=3
    mult=[[[0]*n for _ in range(n)] for _ in range(n)]
    for j in range(n): mult[0][j]=[1 if k==j else 0 for k in range(n)]
    for i in range(n): mult[i][0]=[1 if k==i else 0 for k in range(n)]
    mult[1][1]=[0,0,1]
    return Alg(p,mult,one=0)

for A,label in [(T(3,2),"T_2(F_3)"),(kx3(3),"F_3[x]/x^3"),(T(2,2),"T_2(F_2)")]:
    c,f = brute(A)
    print(f"{label}: brute #der={c} dim={len(A.derivations())} alg.py={A.p**len(A.derivations())}", flush=True)
