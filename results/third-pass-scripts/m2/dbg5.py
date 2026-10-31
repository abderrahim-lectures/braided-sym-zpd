from alg import Alg
def dual(p):
    n=2
    mult=[[[0]*n for _ in range(n)] for _ in range(n)]
    mult[0][0]=[1,0]; mult[0][1]=[0,1]; mult[1][0]=[0,1]; mult[1][1]=[0,0]
    return Alg(p,mult,one=0)
A=dual(3); p,n,N=A.p,A.n,A.p**A.n
els=list(A.elements()); idx={v:i for i,v in enumerate(els)}
print("els",els)
table=[[idx[A.prod(u,v)] for v in els] for u in els]
print("table[0]",table[0], "table[1]",table[1])
add=lambda a,b: idx[tuple((els[a][q]+els[b][q])%p for q in range(n))]
# test the map D(1)=0, D(e)=e  -> code images: D(e_0)=els index of (0,0) = 0 ; D(e_1)= index of (0,1) = ?
print("idx (0,1) =", idx[(0,1)])
import itertools
cnt=0; bad=[]
for code in itertools.product(range(N), repeat=n):
    D=[0]*N
    for u in range(N):
        co=els[u]; out=[0]*n
        for j in range(n):
            if co[j]:
                im=els[code[j]]
                for q in range(n): out[q]=(out[q]+co[j]*im[q])%p
        D[u]=idx[tuple(out)]
    ok=True
    for i in range(n):
        for j in range(n):
            if D[table[i][j]] != add(table[D[i]][j], table[i][D[j]]):
                ok=False
    if ok:
        cnt+=1
        if len(bad)<5: bad.append(code)
print("count",cnt,"first",bad)
# check one of the found maps in detail
code=bad[0]
print("code",code,"D=",[els[D[u]] for u in range(N)])
for i in range(n):
    for j in range(n):
        print(i,j,"prod",els[table[i][j]],"D(prod)",els[D[table[i][j]]],"rhs",els[add(table[D[i]][j],table[i][D[j]])])
