import time
from alg import Alg
def load(path, p, n):
    for line in open(path):
        vals = [int(x) for x in line.split()]
        mult = [[[vals[(i*n+j)*n+k] for k in range(n)] for j in range(n)] for i in range(n)]
        yield Alg(p, mult, name=path, one=0)
def run(path,p,n):
    t0=time.time(); tot=0; nz=0; nz_extra=0; all_extra=0; examples=[]
    for idx,A in enumerate(load(path,p,n)):
        tot+=1
        D=A.derivations(); LD=A.local_derivations()
        dk,dz=A.zpd_data(); isz = (dk==dz)
        if isz: nz+=1
        if len(LD)>len(D):
            if isz: nz_extra+=1
            else: all_extra+=1
            if len(examples)<3: examples.append((idx,isz,len(D),len(LD)))
    print(f"{path}: {tot} algebras, zpd={nz}; local!=der: {nz_extra} zpd cases, {all_extra} non-zpd cases; examples {examples} [{time.time()-t0:.1f}s]")
for path,p,n in [("algs_2_3.txt",2,3),("algs_3_3.txt",3,3),("algs_2_4c.txt",2,4)]:
    run(path,p,n)
