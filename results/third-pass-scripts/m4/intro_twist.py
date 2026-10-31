"""Introduction (HEAD l.138 / worktree l.144) claims the twisted braiding 'has this form'
(mu(x,y) = f(xy) with f linear) 'on a commutative algebra', the twisted braiding being defined
(l.121) 'for a linear map alpha: A -> A'.  Counterexample on a COMMUTATIVE, UNITAL, ZPD algebra.

A = F_p x F_p, represented in the basis e0=(1,1) (the unit) and e1=(1,0); coordinates (a,b)
mean a*e0 + b*e1.  alpha(x,y) := (x+y, 0) is linear; in coordinates alpha(a,b) = (0, 2a+b)."""
from zpdlib import *
from itertools import product

for p in (2,3,5,7):
    # structure constants of F_p x F_p in the basis e0=(1,1), e1=(1,0)
    mult=[[(1,0),(0,1)],     # e0*e0 = e0 ; e0*e1 = e1
          [(0,1),(0,1)]]     # e1*e0 = e1 ; e1*e1 = e1
    A=Alg(2,p,mult,(1,0))
    zpd,dimz,dimk=A.determined()
    alpha=lambda c: (0,(2*c[0]+c[1])%p)           # alpha(a,b) = (0, 2a+b)
    # alpha is linear (given by a matrix) and NOT multiplicative:
    is_mult=all(alpha(A.m(u,v))==A.m(alpha(u),alpha(v)) for u in A.els for v in A.els)
    mu=lambda u,v: tuple((a+b)%p for a,b in zip(A.m(u,v), A.m(alpha(v),alpha(u))))
    if is_mult:
        print(f"p={p}: alpha is multiplicative; witness search *must* fail")
    table={}; witness=None
    for x in A.els:
        for y in A.els:
            pr=A.m(x,y); val=mu(x,y)
            if pr in table and table[pr][0]!=val:
                witness=(table[pr][1],table[pr][0],(x,y),val,pr); break
            table.setdefault(pr,(val,(x,y)))
        if witness: break
    print(f"p={p}: A=F_p x F_p (commutative, unital): zpd={zpd} (dimZ={dimz}, dimker={dimk}); "
          f"alpha linear, multiplicative={is_mult}")
    if witness:
        (xa,ya),va,(xb,yb),vb,pr=witness
        print(f"   same product xy={pr}: (x,y)={xa},{ya} gives mu={va}; (x,y)={xb},{yb} gives mu={vb}"
              f"  -> mu is NOT a function of xy")
