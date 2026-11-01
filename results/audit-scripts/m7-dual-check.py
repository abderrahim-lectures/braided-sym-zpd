#!/usr/bin/env python3
"""Independent check of Example ex:dual (dual numbers K[e]/(e^2), char K != 2) over F_5:
   - mu_alpha(x,y) = xy + alpha(y)alpha(x) with alpha(a+be) = a-be equals f(xy), f(a+be) = 2a;
   - Z_mu = ker mu-bar  (so A IS determined by mu_alpha, as Theorem thm:codim asserts);
   - Z_product != ker product-bar (so A is NOT zpd, as Brešar Theorem 2.27 asserts).
Elements are pairs (a,b) = a + b e over F_p.
"""
P = 5
def add(x,y): return ((x[0]+y[0])%P,(x[1]+y[1])%P)
def mul(x,y): return ((x[0]*y[0])%P,(x[0]*y[1]+x[1]*y[0])%P)
def alpha(x): return (x[0]%P,(-x[1])%P)
def f(x):     return ((2*x[0])%P,0)
def mu_alpha(x,y): return add(mul(x,y), mul(alpha(y),alpha(x)))

def inv(a): return pow(a%P,P-2,P)
def rref(rows,nc):
    M=[list(r) for r in rows]; piv=[]; r=0
    for c in range(nc):
        p=None
        for i in range(r,len(M)):
            if M[i][c]%P: p=i;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        k=inv(M[r][c]); M[r]=[(k*t)%P for t in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]%P:
                q=M[i][c]; M[i]=[(M[i][j]-q*M[r][j])%P for j in range(nc)]
        piv.append(c); r+=1
        if r==len(M): break
    return M[:r],piv
def rank(rows,nc): return len(rref(rows,nc)[1])
def kernel(rows,nc):
    R,piv=rref(rows,nc); free=[c for c in range(nc) if c not in piv]; K=[]
    for fr in free:
        v=[0]*nc; v[fr]=1
        for i,c in enumerate(piv): v[c]=(-R[i][fr])%P
        K.append(tuple(v))
    return K
def inspan(v,basis):
    if not basis: return all(t%P==0 for t in v)
    return rank([list(b) for b in basis]+[list(v)],len(v))==rank([list(b) for b in basis],len(v))
def tensor(x,y):   # x (x) y in the basis 1,e of A
    return (x[0]*y[0]%P, x[0]*y[1]%P, x[1]*y[0]%P, x[1]*y[1]%P)
EL=[(a,b) for a in range(P) for b in range(P)]
BASIS=[(1,0),(0,1)]

for name,mu in (("mu_alpha",mu_alpha),("product",mul)):
    rows=[[mu(BASIS[i],BASIS[j])[r] for i in range(2) for j in range(2)] for r in range(2)]
    kb=kernel(rows,4); rk=rank(rows,4)
    zs=[tensor(x,y) for x in EL for y in EL if mu(x,y)==(0,0)]
    sp=rank([list(v) for v in zs],4)
    print(f"{name}: rank mu-bar={rk}, dim ker={4-rk}, #zero pairs={len(zs)}, dim span{{x(x)y}}={sp}, "
          f"span<=ker:{all(inspan(v,kb) for v in zs)}, Z==ker: {sp==4-rk}")
print("alpha involutive automorphism:", all(alpha(alpha(x))==x for x in EL)
      and all(alpha(mul(x,y))==mul(alpha(x),alpha(y)) for x in EL for y in EL))
print("mu_alpha(x,y) == f(xy) for all x,y:", all(mu_alpha(x,y)==f(mul(x,y)) for x in EL for y in EL))
print("f(1) =", f((1,0)), " f(1+e)=", f((1,1)), " ker f =", [x for x in EL if f(x)==(0,0)])
print("idempotents of A:", [x for x in EL if mul(x,x)==x])
print("E [=K e] is a two-sided ideal of codim 1 not containing 1:",
      all(mul(n,b)[1]%(P)==mul(n,b)[1] for n in [(0,1),(0,2),(0,3),(0,4)] for b in EL))
