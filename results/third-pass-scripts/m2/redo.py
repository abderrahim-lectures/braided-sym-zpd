import time
from build2 import M, T
from alg import Alg
def report(A):
    t0=time.time(); d1,d2=A.zpd_data(); D=A.derivations(); LD=A.local_derivations()
    print(f"{A.name:14s} p={A.p} n={A.n:2d} unit={A.unit_coords} zpd={d1==d2} ({d1},{d2}) dimDer={len(D):2d} dimLDer={len(LD):2d} {'EXTRA!' if len(LD)>len(D) else 'equal'} [{time.time()-t0:.1f}s]", flush=True)
for p in (2,3,5):
    report(T(p,2))
for p in (2,3):
    report(M(p,2))
    report(T(p,3))
report(T(2,4))
