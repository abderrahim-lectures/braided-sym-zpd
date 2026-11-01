from build import full_matrix_units, from_mats, upper_triangular_units
from alg import Alg
p=2
mats=full_matrix_units(p,2)
A=from_mats(p,mats,"M2")
print("basis order: I, E11, E12, E21, E22")
for i in range(A.n):
    for j in range(A.n):
        print(" e_%d*e_%d = %s"%(i,j,A.mult[i][j]))
