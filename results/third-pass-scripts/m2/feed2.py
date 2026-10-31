import subprocess
from build2 import M, T, alg_from_spanning
from build import product_of_fields
from alg import Alg
def feed(A,label):
    n=A.n
    s="%d %d\n"%(A.p,n)+" ".join(str(x) for i in range(n) for j in range(n) for x in A.mult[i][j])
    o=subprocess.run(["./bruteder"],input=s,capture_output=True,text=True)
    cnt=int(o.stdout); dim=0; q=1
    while q<cnt: q*=A.p; dim+=1
    ok = (cnt == A.p**len(A.derivations()))
    print(f"{label}: #der={cnt}={A.p}^{dim} alg.py dim={len(A.derivations())} {'AGREE' if ok else 'DISAGREE'}", flush=True)
feed(T(3,2),"T_2(F_3)")
feed(T(2,2),"T_2(F_2)")
feed(M(2,2),"M_2(F_2)")
feed(product_of_fields(2,2),"K^2(F_2)")
feed(product_of_fields(3,2),"K^2(F_3)")
feed(product_of_fields(2,3),"K^3(F_2)")
# F_p[x]/x^3
def kx3(p):
    n=3
    mult=[[[0]*n for _ in range(n)] for _ in range(n)]
    for j in range(n): mult[0][j]=[1 if k==j else 0 for k in range(n)]
    for i in range(n): mult[i][0]=[1 if k==i else 0 for k in range(n)]
    mult[1][1]=[0,0,1]
    return Alg(p,mult,one=0)
feed(kx3(3),"F_3[x]/x^3")
feed(kx3(2),"F_2[x]/x^3")
