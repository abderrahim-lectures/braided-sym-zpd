from build import product_of_fields
from linmod import nullspace, rank, span_basis
A = product_of_fields(3,2)
p,n = A.p,A.n
brows=[]
for x in A.elements():
    if not any(x): continue
    mrows = [[sum(x[i]*A.mult[i][j][l] for i in range(n))%p for j in range(n)] for l in range(n)]
    ker = nullspace(mrows,p,n)
    assert all(not any(A.prod(x,y)) for y in ker)
    for y in ker:
        brows.append([x[i]*y[j]%p for i in range(n) for j in range(n)])
print("num rows", len(brows), "rank", rank(brows,p,n*n))
# brute force annihilator
tvecs=[]
for x in A.elements():
    for y in A.elements():
        if not any(A.prod(x,y)):
            t=[0]*(n*n)
            for i in range(n):
                for j in range(n): t[i*n+j]=(x[i]*y[j])%p
            tvecs.append(t)
Zb = span_basis(tvecs,p,n*n)
print("dimZ brute", len(Zb))
ann = nullspace(Zb,p,n*n)
print("dim Z^perp", len(ann))
# check: does every row lie in Z^perp? i.e. is every B in annihilator orthogonal to my rows?
for B in ann:
    for r in brows:
        if sum(a*b for a,b in zip(B,r))%p: print("row not killed by valid B:", r, B); break
