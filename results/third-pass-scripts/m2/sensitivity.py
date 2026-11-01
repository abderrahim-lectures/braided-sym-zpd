from alg import Alg
p,n=3,3
mult=[[[0]*n for _ in range(n)] for _ in range(n)]
for j in range(n): mult[0][j]=[1 if k==j else 0 for k in range(n)]
for i in range(n): mult[i][0]=[1 if k==i else 0 for k in range(n)]
mult[1][1]=[0,0,1]
A=Alg(p,mult,one=0)
print("A = F_3[x]/x^3; zpd dims (ker mubar, Z_mu) =", A.zpd_data(), "-> zpd:", A.zpd_data()[0]==A.zpd_data()[1])
print("dim Der =", len(A.derivations()), " dim LDer =", len(A.local_derivations()))
M=[[0,0,0],[1,0,0],[0,0,0]]   # D(1)=0, D(x)=1, D(x^2)=0
print("is a derivation?", A.is_derivation(M))
print("locality failures over all 27 elements (span test):", A.check_local(M))
print("-> a local derivation that is not a derivation, on a NON-zpd unital algebra")
