import subprocess, sys
from build import full_matrix_units, upper_triangular_units, from_mats, product_of_fields
from alg import Alg
def feed(A, label):
    n=A.n
    s="%d %d\n"%(A.p,n)
    for i in range(n):
        for j in range(n):
            s+=" ".join(str(x) for x in A.mult[i][j])+" "
    out=subprocess.run(["./bruteder"],input=s,capture_output=True,text=True)
    cnt=int(out.stdout)
    dim=0; q=1
    while q<cnt: q*=A.p; dim+=1
    print(f"{label}: #derivations={cnt} = {A.p}^{dim}   (alg.py dimDer={len(A.derivations())})")
for p in (2,3):
    feed(from_mats(p, full_matrix_units(p,2), "M2"), "M_2(F_%d)"%p)
    feed(from_mats(p, upper_triangular_units(p,2), "T2"), "T_2(F_%d)"%p)
feed(from_mats(2, upper_triangular_units(2,3), "T3"), "T_3(F_2)")
for p in (2,3):
    feed(product_of_fields(p,2), "K^2(F_%d)"%p)
# K[x]/x^3
def kx3(p):
    n=3
    mult=[[[0]*n for _ in range(n)] for _ in range(n)]
    mult[0]=[[1,0,0],[0,1,0],[0,0,1]]
    for i in range(n): mult[i][0]=[1 if k==i else 0 for k in range(n)]
    mult[1][1]=[0,0,1]
    return Alg(p,mult,one=0)
feed(kx3(2), "F_2[x]/x^3"); feed(kx3(3), "F_3[x]/x^3")
