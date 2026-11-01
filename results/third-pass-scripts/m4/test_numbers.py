"""Re-verify the numerical/structural claims of v8 Sections 4-5 (independent implementation)."""
from zpdlib import *
from itertools import product
import sys

def unflat(v,n): return tuple(tuple(v[i*n+j] for j in range(n)) for i in range(n))
def flat(M): return tuple(M[i][j] for i in range(len(M)) for j in range(len(M)))
def mm(X,Y,p):
    n=len(X)
    return tuple(tuple(sum(X[i][t]*Y[t][j] for t in range(n))%p for j in range(n)) for i in range(n))
def bas(d,k): return tuple(1 if i==k else 0 for i in range(d))
def alg_from_mu(d,p,mu): return Alg(d,p,[[mu(bas(d,a),bas(d,b)) for b in range(d)] for a in range(d)])
def report(name,A,count=False):
    det,dimz,dimk=A.determined()
    zero=sum(1 for x in A.els for y in A.els if all(v==0 for v in A.m(x,y))) if count else None
    print(f" {name}: rank mu-bar={A.mu_rank()}, dim ker={dimk}, dim Z={dimz}, determined={det}"
          + (f", #zero pairs={zero}" if count else ""), flush=True)

print("=== prop:matrix: A=M_2(F_p), alpha = conjugation by diag(1,-1), mu(x,y)=xy+alpha(yx) ===", flush=True)
for p in (3,5):
    d=4
    m2=lambda u,v: flat(mm(unflat(u,2),unflat(v,2),p))
    D=((1,0),(0,(p-1)%p)); Di=((1,0),(0,pow((p-1)%p,p-2,p)))
    alpha=lambda u: flat(mm(mm(D,unflat(u,2),p),Di,p))
    mu=lambda u,v: tuple((a+b)%p for a,b in zip(m2(u,v),alpha(m2(v,u))))
    A=alg_from_mu(d,p,mu)
    report(f"M_2(F_{p}), twisted xy+alpha(yx)",A,count=(p==3))

print()
print("=== A=M_2(F_p): ordinary product and transpose twist xy+(xy)^T ===", flush=True)
for p in (2,3,5):
    d=4
    m2=lambda u,v: flat(mm(unflat(u,2),unflat(v,2),p))
    A=alg_from_mu(d,p,m2); report(f"ordinary product M_2(F_{p})",A,count=(p==3))
    tr=lambda u: (u[0],u[2],u[1],u[3])
    mutr=lambda u,v: tuple((a+b)%p for a,b in zip(m2(u,v),tr(m2(u,v))))
    B=alg_from_mu(d,p,mutr); report(f"transpose twist xy+(xy)^T, p={p}",B,count=(p==3))

print()
print("=== ex:dual: A=K[eps]/(eps^2), mu(x,y)=(id+alpha)(xy)=2*x0*y0 ===", flush=True)
for p in (3,5,7):
    prod=lambda u,v: (u[0]*v[0]%p, (u[0]*v[1]+u[1]*v[0])%p)
    A=alg_from_mu(2,p,prod); report(f"dual numbers, ordinary product, p={p}",A)
    mu=lambda u,v: (2*u[0]*v[0]%p, 0)
    B=alg_from_mu(2,p,mu); report(f"dual numbers, twisted product (id+alpha)(xy), p={p}",B)
    print(f"   idempotents: {[x for x in A.els if A.m(x,x)==x]}", flush=True)
