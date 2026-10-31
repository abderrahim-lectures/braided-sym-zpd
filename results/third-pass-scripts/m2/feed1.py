import subprocess
from build import full_matrix_units, upper_triangular_units, from_mats, product_of_fields
from alg import Alg
def feed(A,label):
    n=A.n
    s="%d %d\n"%(A.p,n)+" ".join(str(x) for i in range(n) for j in range(n) for x in A.mult[i][j])
    o=subprocess.run(["./bruteder"],input=s,capture_output=True,text=True)
    cnt=int(o.stdout); dim=0; q=1
    while q<cnt: q*=A.p; dim+=1
    print(f"{label}: #der={cnt}={A.p}^{dim} alg.py={len(A.derivations())}", flush=True)
feed(from_mats(2, full_matrix_units(2,2), "M2"), "M_2(F_2)")
feed(from_mats(2, upper_triangular_units(2,2), "T2"), "T_2(F_2)")
feed(from_mats(3, upper_triangular_units(3,2), "T2"), "T_2(F_3)")
feed(from_mats(2, upper_triangular_units(2,3), "T3"), "T_3(F_2)")
feed(product_of_fields(2,2), "K^2(F_2)")
feed(product_of_fields(3,2), "K^2(F_3)")
