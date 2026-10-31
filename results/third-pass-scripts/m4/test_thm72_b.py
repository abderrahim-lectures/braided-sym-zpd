"""Exhaustive test of the paper's recalled Theorem 7.2 (thm:bresar-zpp) on A = B = M_2(F_2)."""
from zpdlib import *
from itertools import product
p=2; n=2
A=matrix_units_alg(n,p)
ok,dz,dk=A.determined()
print("M_2(F_2) is zpd:",ok,"(dim Z =",dz,", dim ker =",dk,")")
def flat(M): return tuple(M[i][j] for i in range(n) for j in range(n))
def unflat(v): return tuple(tuple(v[i*n+j] for j in range(n)) for i in range(n))
def mm(X,Y): return tuple(tuple(sum(X[i][t]*Y[t][j] for t in range(n))%p for j in range(n)) for i in range(n))
e=[unflat(tuple(1 if k==t else 0 for k in range(n*n))) for t in range(n*n)]
ONE=unflat(tuple(1 if i==j else 0 for i in range(n) for j in range(n)))
ZERO=unflat(tuple(0 for _ in range(n*n)))
def det(M): return (M[0][0]*M[1][1]-M[0][1]*M[1][0])%p
def inv(M):
    di=pow(det(M),p-2,p)
    return ((M[1][1]*di%p,(-M[0][1])*di%p),((-M[1][0])*di%p,M[0][0]*di%p))
GL=[unflat(v) for v in product(range(p),repeat=n*n) if det(unflat(v))]
def phi_of_images(imgs):
    def phi(X):
        v=flat(X); res=[[0]*n for _ in range(n)]
        for a in range(n*n):
            if v[a]:
                for i in range(n):
                    for j in range(n): res[i][j]=(res[i][j]+imgs[a][i][j])%p
        return tuple(tuple(r) for r in res)
    return phi
cands=[('zero',phi_of_images([ZERO]*4))]
for S in GL:
    Si=inv(S); cands.append(('Ad_S',phi_of_images([mm(mm(Si,e[a]),S) for a in range(4)])))
for nm,phi in cands:
    if nm!='zero':
        assert all(phi(mm(e[a],e[b]))==mm(phi(e[a]),phi(e[b])) for a in range(4) for b in range(4))
print("#homomorphisms enumerated:",len(cands))
def image_elements(T):
    imgs=[T(e[a]) for a in range(4)]; out=set()
    for coeffs in product(range(p),repeat=4):
        res=[[0]*n for _ in range(n)]
        for a in range(4):
            if coeffs[a]:
                for i in range(n):
                    for j in range(n): res[i][j]=(res[i][j]+imgs[a][i][j])%p
        out.add(tuple(tuple(r) for r in res))
    return out
def zpp(T):
    imgs=[tuple(T(e[a])[i][j] for i in range(n) for j in range(n)) for a in range(4)]
    for x in A.els:
        X=unflat(x)
        Lx=[flat(mm(X,e[a])) for a in range(4)]
        for k in kernel(Lx,4,p):
            if mm(T(X),T(unflat(k)))!=ZERO: return False
    return True
count_zpp=0; count_hyp=0; bad_c=0; bad_phi=0; ex=[]
for v in product(range(p),repeat=16):
    T=phi_of_images([unflat(v[4*a:4*a+4]) for a in range(4)])
    if not zpp(T): continue
    count_zpp+=1
    if not any(det(u) for u in image_elements(T)): continue
    count_hyp+=1
    c=T(ONE)
    if det(c)==0:
        bad_c+=1
        if len(ex)<5: ex.append(('T(1) singular',v))
        continue
    if not any(all(mm(c,phi(e[a]))==T(e[a]) and mm(phi(e[a]),c)==T(e[a]) for a in range(4)) for nm,phi in cands):
        bad_phi+=1
        if len(ex)<5: ex.append(('no phi',v))
print("linear maps T:",p**16)
print("zpp maps:",count_zpp)
print("zpp and range contains an invertible:",count_hyp)
print("   with T(1) singular:",bad_c)
print("   with T(1) invertible but no phi: ",bad_phi)
print("examples:",ex)
