from alg import Alg
p,n=3,3
lines=open("algs_3_3.txt").read().split("\n")
idx=3
vals=[int(x) for x in lines[idx].split()]
mult=[[[vals[(i*n+j)*n+k] for k in range(n)] for j in range(n)] for i in range(n)]
A=Alg(p,mult,one=0)
print("mult table (e0=1,e1,e2):")
for i in range(n): print("  ", i, [A.mult[i][j] for j in range(n)])
print("zpd_data", A.zpd_data())
print("idempotents", A.idempotents())
D=A.derivations(); LD=A.local_derivations()
print("dim Der",len(D),"dim LDer",len(LD))
for M in LD:
    isd,wit=A.is_derivation(M)
    if not isd:
        print("local non-derivation M rows (D(e_j) coords):",M,"fails at",wit)
        print("direct check:", A.check_local(M)[:3])
        break
