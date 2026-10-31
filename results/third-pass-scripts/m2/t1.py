import time
from build import full_matrix_units, upper_triangular_units, product_of_fields, from_mats
from alg import Alg

def report(A):
    t0=time.time()
    assert A.is_associative(), (A.name, "not associative")
    d1,d2 = A.zpd_data()
    D = A.derivations()
    LD = A.local_derivations()
    print(f"{A.name:14s} p={A.p} n={A.n} assoc=Y zpd_dim=({d1},{d2}) zpd={d1==d2} dimDer={len(D)} dimLDer={len(LD)} {'LOCAL!=DER' if len(LD)>len(D) else 'equal'} [{time.time()-t0:.1f}s]", flush=True)
    return D, LD

for p in (2,3,5):
    A = from_mats(p, upper_triangular_units(p,2), "T2(F%d)"%p)
    report(A)
for p in (2,3):
    A = from_mats(p, upper_triangular_units(p,3), "T3(F%d)"%p)
    report(A)
for p in (2,3):
    A = from_mats(p, full_matrix_units(p,2), "M2(F%d)"%p)
    report(A)
for p in (2,3,5):
    for m in (2,3,4):
        A = product_of_fields(p,m)
        report(A)
