"""Exp 13: the SHARP form of thm:zpd-fxy, derived and machine-validated.

Claim. A associative zpd (no unitality needed), f : A -> A linear, mu = f o m. Then
   A determined by mu   <=>   span{xy : xy in K} = A^2 cap K,      K = ker f.
Proof. Z := span{x (x) y : xy = 0} = ker mbar (zpd). Z <= Zs_mu, and mubar : A(x)A -> A^2 is onto,
so Zs_mu / Z = span{xy : xy in K} and ker mubar_mu / Z = A^2 cap K. Hence Zs_mu = ker mubar_mu iff
the two subspaces agree.  If A has a right identity, u in A^2 cap K gives u = u*1 with f(u) = 0, so
u is itself a product in K and the condition holds for every f (this is the unital theorem).
Validate the equivalence directly against the exact determination test.
"""
import itertools, alg

def is_assoc(T,p):
    n = len(T)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                a = alg.mul_from(T, T[i][j], tuple(1 if s==k else 0 for s in range(n)), p)
                b = alg.mul_from(T, tuple(1 if s==i else 0 for s in range(n)), T[j][k], p)
                if a != b: return False
    return True

def condition(T,f,p):
    n = len(T)
    pts = list(itertools.product(range(p), repeat=n))
    A2 = alg.span_basis([alg.mul_from(T,x,y,p) for x in pts for y in pts], p)
    K  = alg.span_basis(alg.kernel_basis([[alg.apply_lin(f,tuple(1 if k==j else 0 for k in range(n)),p)[i] for j in range(n)] for i in range(n)], p, n), p)
    s = alg.span_basis([alg.mul_from(T,x,y,p) for x in pts for y in pts
                        if alg.in_span(alg.mul_from(T,x,y,p), K, p)], p)
    capped = alg.span_basis([v for v in pts if alg.in_span(v,K,p) and alg.in_span(v,A2,p)], p)
    if len(s) != len(capped): return False
    return all(alg.in_span(v, s, p) for v in capped)

def linear_maps(p,n):
    for imgs in itertools.product(itertools.product(range(p), repeat=n), repeat=n):
        yield tuple(tuple(v) for v in imgs)

def run(T,p,label,allf=True):
    n = len(T)
    z = alg.determined(T,p)[0]
    if not z:
        print(f"  {label}: not zpd, skipped"); return
    bad = 0; cnt = 0
    for f in linear_maps(p,n) if allf else []:
        cnt += 1
        d1 = alg.determined(alg.compose_Mu(f,T,n,p),p)[0]
        d2 = condition(T,f,p)
        if d1 != d2:
            bad += 1
            print("   MISMATCH:", label, f, d1, d2)
    print(f"  {label}: zpd, {cnt} linear f, mismatches between determination and the product condition: {bad}")

def comm_structures(p,n):
    pairs=[(i,j) for i in range(n) for j in range(i,n)]
    for vals in itertools.product(itertools.product(range(p),repeat=n), repeat=len(pairs)):
        T=[[[0]*n for _ in range(n)] for _ in range(n)]
        for (ij,v) in zip(pairs,vals):
            i,j=ij; T[i][j]=[x%p for x in v]; T[j][i]=[x%p for x in v]
        yield T

def unital_structures(p, n):
    free = [(i,j) for i in range(1,n) for j in range(1,n)]
    for vals in itertools.product(itertools.product(range(p), repeat=n), repeat=len(free)):
        T = [[[0]*n for _ in range(n)] for _ in range(n)]
        for k in range(n):
            T[0][k][k] = 1 % p; T[k][0][k] = 1 % p
        for (ij, v) in zip(free, vals):
            i,j = ij; T[i][j] = [x % p for x in v]
        yield T

print("(a) all commutative associative algebras dim<=3 over F_2:")
cnt=0
for T in comm_structures(2,3):
    if is_assoc(T,2) and alg.determined(T,2)[0]: cnt+=1
print("   count:", cnt)
print("(b) validate the equivalence on: M1's non-unital counterexample algebra, T_2(F_2), F_2 x F_2")
n=3; p=2
T = [[[0]*n for _ in range(n)] for _ in range(n)]
T[0][0][0]=1; T[0][1][2]=1; T[0][2][2]=1; T[1][0][1]=1; T[1][0][2]=1
run(T,p,"M1 algebra over F_2")
n=3; p=2
Tt = [[[0]*n for _ in range(n)] for _ in range(n)]
Tt[0][0][0]=1; Tt[1][1][0]=0; Tt[1][1][1]=1; Tt[1][1][2]=0
# T_2(F_2): basis e11,e12,e22
T2 = [[[0]*3 for _ in range(3)] for _ in range(3)]
T2[0][0][0]=1; T2[0][1][1]=1; T2[1][2][1]=1; T2[2][2][2]=1
run(T2,p,"T_2(F_2)")
# F_2 x F_2
T3 = [[[0]*2 for _ in range(2)] for _ in range(2)]
T3[0][0][0]=1; T3[1][1][1]=1
run(T3,p,"F_2 x F_2")
print()
print("(c) exhaustive: every unital associative algebra dim<=3 over F_2, every f")
tot=0
for T in unital_structures(2,3):
    if not is_assoc(T,2) or not alg.determined(T,2)[0]: continue
    tot+=1
run([[[0]]],2,"skip") if False else None
print("   unital zpd algebras:", tot, "(each checked inside the loop below)")
bad=0
for T in unital_structures(2,3):
    if not is_assoc(T,2) or not alg.determined(T,2)[0]: continue
    for f in linear_maps(2,3):
        d1 = alg.determined(alg.compose_Mu(f,T,3,2),2)[0]
        d2 = condition(T,f,2)
        if d1 != d2: bad+=1
print("   mismatches over all (A,f):", bad)
