import time
from build import from_mats, full_matrix_units, upper_triangular_units, product_of_fields
from alg import Alg
from linmod import span_basis

def report(A, note=""):
    t0=time.time()
    d1,d2 = A.zpd_data(); D=A.derivations(); LD=A.local_derivations()
    print(f"{A.name:22s} p={A.p} n={A.n:2d} zpd={d1==d2} (ker,Z)=({d1},{d2}) dimDer={len(D):2d} dimLDer={len(LD):2d} {'EXTRA' if len(LD)>len(D) else 'equal'} [{time.time()-t0:.1f}s] {note}", flush=True)
    return len(LD)>len(D)

# T_4(F_2): dim 10
report(from_mats(2, upper_triangular_units(2,4), "T4(F2)"))
# T_2 x T_2 over F_2 and F_3 (dim 8 / 8)
def prod_alg(p, b1, b2, name):
    # basis: (e_i,0) then (0,f_j) with (e_0,0) identity?  Use identity = (1,1) as first element
    n1,n2 = len(b1), len(b2)
    m = n1+n2
    mult = [[[0]*m for _ in range(m)] for _ in range(m)]
    # elements: index 0 = (1,1); 1..n1-1 = (e_i,0); n1..m-1 = (0,f_j)
    def put(vec, i, j):
        for k in range(m): mult[i][j][k] = vec[k] % p
    # build multiplication table via temporary Alg objects for the factors
    A1 = from_mats(p, b1, "b1"); A2 = from_mats(p, b2, "b2")
    ids = [ (list(range(m))) ]
    def coords1(i):   # element index -> coords in A1 x A2
        v=[0]*m
        if i==0: v[0]=1
        elif i<n1: v[i]=1
        else: v[i]=1
        return v
    # simpler: define product on the basis abstractly using the factor tables
    for i in range(m):
        for j in range(m):
            out=[0]*m
            if i==0: out[j]=(out[j]+1)%p
            elif j==0: out[i]=(out[i]+1)%p
            # now the "non-unit" parts
            ai = None if i==0 else ('a',i-1) if i<n1 else ('b',i-n1)
            bj = None if j==0 else ('a',j-1) if j<n1 else ('b',j-n1)
            if ai is None or bj is None: pass
            else:
                va, ta = ai; vb, tb = bj
                if ta=='a' and tb=='a':
                    c = A1.mult[va][vb]
                    for k in range(n1-1 if False else A1.n):
                        if c[k]:
                            idx = 0 if k==0 else k
                            out[idx]=(out[idx]+c[k])%p
                elif ta=='b' and tb=='b':
                    c = A2.mult[va][vb]
                    for k in range(A2.n):
                        if c[k]:
                            idx = 0 if k==0 else n1+k-1
                            out[idx]=(out[idx]+c[k])%p
            for k in range(m): mult[i][j][k]=out[k]%p
    return Alg(p, mult, name=name, one=0)

report(prod_alg(2, upper_triangular_units(2,2), upper_triangular_units(2,2), "T2xT2 (F2)"))
report(prod_alg(3, upper_triangular_units(3,2), product_of_fields(3,2).mult, "T2 x K^2 (F3)"))
