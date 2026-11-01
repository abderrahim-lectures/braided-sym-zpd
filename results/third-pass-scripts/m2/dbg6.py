from alg import Alg
p,n=3,3
mult=[[[0]*n for _ in range(n)] for _ in range(n)]
for j in range(n): mult[0][j]=[1 if k==j else 0 for k in range(n)]
for i in range(n): mult[i][0]=[1 if k==i else 0 for k in range(n)]
mult[1][1]=[0,0,1]
A=Alg(p,mult,one=0)
D=A.derivations()
print("dim Der", len(D))
for d in D: print("  der:", d)
LD=A.local_derivations()
print("dim LDer", len(LD))
for M in LD:
    ok,_=A.is_derivation(M)
    bad=A.check_local(M)
    print("  M:",M,"derivation?",ok,"locality failures:",len(bad), bad[:2])
# check V_a for a = x + x^2
for a in [(0,1,1),(0,1,0),(0,1,2)]:
    imgs=[A.apply(d,a) for d in D]
    print("a=",a,"V_a span:",imgs)
    print("   D(a) for the suspicious map:", A.apply([[0,0,0],[1,0,0],[0,0,0]],a))
