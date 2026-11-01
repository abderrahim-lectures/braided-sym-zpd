import sys, time
from alg import Alg

def load(path, p, n):
    for line in open(path):
        vals = [int(x) for x in line.split()]
        assert len(vals) == n*n*n, (len(vals), n)
        mult = [[[vals[(i*n+j)*n+k] for k in range(n)] for j in range(n)] for i in range(n)]
        yield Alg(p, mult, name=path, one=0)

def run(path, p, n, verbose=False):
    t0=time.time(); nz=0; bad=[]
    for idx, A in enumerate(load(path,p,n)):
        dk,dz = A.zpd_data()
        if dk != dz: continue
        nz += 1
        D = A.derivations(); LD = A.local_derivations()
        if len(LD) > len(D):
            bad.append((idx, A, len(D), len(LD)))
    print(f"{path}: zpd={nz}  local-non-derivation cases={len(bad)}  [{time.time()-t0:.1f}s]", flush=True)
    for idx,A,d1,d2 in bad:
        print("  algebra #%d dimDer=%d dimLDer=%d  mult=%s" % (idx,d1,d2,A.mult))
        for M in A.local_derivations():
            isd, wit = A.is_derivation(M)
            if not isd:
                print("   witness local non-derivation M=%s, fails at pair %s" % (M, wit))
                badpairs = A.check_local(M)
                print("   direct locality check failures:", badpairs[:5])
                break
    return bad

if __name__ == "__main__":
    for path,p,n in [("algs_2_2.txt",2,2),("algs_3_2.txt",3,2),("algs_5_2.txt",5,2),
                     ("algs_2_3.txt",2,3),("algs_3_3.txt",3,3),("algs_2_4c.txt",2,4)]:
        run(path,p,n)
