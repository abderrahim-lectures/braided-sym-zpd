from build import product_of_fields
from linmod import nullspace, rank
A = product_of_fields(3,2)
p,n = A.p,A.n
# x = u : coords (0,1,0)
x = (0,1,0)
mrows = [[sum(x[i]*A.mult[i][j][l] for i in range(n))%p for j in range(n)] for l in range(n)]
print("mrows", mrows)
ker = nullspace(mrows,p,n)
print("ker", ker)
for y in ker: print("prod", A.prod(x,y))
for i in range(n):
    for j in range(n):
        if A.mult[i][j] == (0,0,0): print("zero basis pair", i,j)
