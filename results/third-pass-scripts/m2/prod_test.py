"""Counterexample candidate: A = T_2(F_p) x F_p, D(b,c) = (c*delta(b), 0)."""
from build import from_mats
from alg import Alg
from linmod import rank, span_basis

def blocks(p):
    # basis of T_2 x F_p inside M_3(F_p): 1 = I3, then E11, E12, E22, E33
    def E(i,j):
        M=[[0]*3 for _ in range(3)]; M[i][j]=1; return M
    def sm(a,b,c,d,e):
        return [[a, b, 0],[c, d, 0],[0,0,e]]
    basis = [sm(1,0,0,1,1)]                     # the identity
    basis.append(sm(1,0,0,0,0))                 # E11
    basis.append(sm(0,1,0,0,0))                 # E12
    basis.append(sm(0,0,0,1,0))                 # E22
    basis.append(sm(0,0,0,0,1))                 # E33
    return basis

for p in (2,3,5,7):
    A = from_mats(p, blocks(p), "T2 x F%d"%p)
    dk,dz = A.zpd_data()
    D = A.derivations(); LD = A.local_derivations()
    print(f"p={p}: zpd_dim=({dk},{dz}) zpd={dk==dz} dimDer={len(D)} dimLDer={len(LD)} extra={len(LD)-len(D)}")
    # explicit candidate: D(b,c) = c*delta(b) where delta = inner derivation by E12
    # coordinates: e0=1, e1=E11, e2=E12, e3=E22, e4=E33;  b = b0*1 + b1*E11 + b2*E12 + b3*E22,
    # c = coordinate of E33 ; new element (b,c) has coords (b0, b1, b2, b3, c)
    # delta = inner by E12: delta(x) = E12 x - x E12
    A_ = A
    def prod(x,y): return A_.prod(x,y)
    def delta(x):
        E12 = A_.unit(2)
        return tuple((a-b)%p for a,b in zip(prod(E12,x), prod(x,E12)))
    def Dmap(a):
        b = (a[0],a[1],a[2],a[3],0); c = a[4]
        d = delta(b)
        return tuple([(c*d[k])%p for k in range(4)]+[0])
    isd, wit = A.is_derivation([list(row) for row in [ [Dmap(A.unit(j))[k] for k in range(5)] for j in range(5)]])
    print("   candidate is derivation?", isd, "fails at", wit)
    bad = A.check_local([[Dmap(A.unit(j))[k] for k in range(5)] for j in range(5)])
    print("   candidate locality failures (direct exhaustive check):", len(bad))
    if bad: print("     e.g.", bad[0])
