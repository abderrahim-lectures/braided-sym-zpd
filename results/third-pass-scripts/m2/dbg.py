from build import product_of_fields
from linmod import nullspace, rank
from alg import Alg
import itertools

def brute_zpd(A):
    p,n = A.p,A.n
    tvecs=[]
    for x in A.elements():
        for y in A.elements():
            if not any(A.prod(x,y)):
                t=[0]*(n*n)
                for i in range(n):
                    for j in range(n):
                        t[i*n+j]=(x[i]*y[j])%p
                tvecs.append(t)
    return rank(tvecs,p,n*n)

A = product_of_fields(3,2)
print("K^2 brute dimZ:", brute_zpd(A), "zpd_data:", A.zpd_data())
