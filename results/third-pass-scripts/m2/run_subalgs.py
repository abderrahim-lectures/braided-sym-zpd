import sys, time
from subalgs import enumerate_subalgebras, unflat
from build import from_mats
from linmod import rank

p=int(sys.argv[1]); d=int(sys.argv[2]); dims=[int(x) for x in sys.argv[3].split(",")]; k=int(sys.argv[4])
t0=time.time(); cnt=0; nz=0; extra=[]
seen_struct=set()
for basis in enumerate_subalgebras(p,d,dims,k):
    cnt+=1
    A = from_mats(p, basis, "sub", one=0)
    key = tuple(sorted(tuple(sorted(map(tuple,row))) for row in A.mult))
    if key in seen_struct: continue
    seen_struct.add(key)
    dk,dz = A.zpd_data()
    if dk!=dz: continue
    nz+=1
    D=A.derivations(); LD=A.local_derivations()
    if len(LD)>len(D):
        extra.append((len(D),len(LD),A.mult))
print(f"p={p} ambient M_{d}: {cnt} subalgebras, {len(seen_struct)} distinct tables, {nz} zpd, extra={len(extra)} [{time.time()-t0:.0f}s]")
for e in extra[:5]: print("  ", e[0], e[1], e[2])
