# Counterexample to the v9 criterion sentence (abstract l.110, Introduction l.159):
# A = M_2(F_3), sigma = swap (x(x)y = xy+yx = x o y), D = inner derivation x -> a x - x a, a = e12.
# Hypothesis of the sentence: the Leibniz defect  Delta(x,y) = D(x o y) - D(x) o y - x o D(y)
# vanishes on the pairs with x o y = 0.  Here Delta == 0, so the hypothesis holds and the factor
# S of Delta (Delta = S o overline{o}) is S = 0 (unique, because overline{o} is onto).
# The sentence then claims: D is a braided-symmetric derivation  <=>  S agrees with D on products.
# D IS a derivation, but S(x o y) = 0 != D(x o y) for x = e21, y = e11.
p = 3
def mul(x,y):
    a,b,c,d = x; e,f,g,h = y
    return ((a*e+b*g)%p,(a*f+b*h)%p,(c*e+d*g)%p,(c*f+d*h)%p)
def add(x,y): return tuple((u+v)%p for u,v in zip(x,y))
def neg(x): return tuple((-u)%p for u in x)
def sm(c,x): return tuple((c*u)%p for u in x)
def rank(rows):
    rows=[[v%p for v in r] for r in rows]; m=len(rows); r=0; n=len(rows[0])
    for c in range(n):
        piv=next((i for i in range(r,m) if rows[i][c]),None)
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][c],-1,p); rows[r]=[(v*inv)%p for v in rows[r]]
        for i in range(m):
            if i!=r and rows[i][c]:
                f=rows[i][c]; rows[i]=[(a-f*b)%p for a,b in zip(rows[i],rows[r])]
        r+=1
        if r==m: break
    return r
E = {(i,j): tuple(1 if (r,c)==(i,j) else 0 for r in range(2) for c in range(2)) for i in range(2) for j in range(2)}
def jor(x,y): return add(mul(x,y),mul(y,x))
def jorbar_cols(): return [jor(E[(i,j)],E[(k,l)]) for i in range(2) for j in range(2) for k in range(2) for l in range(2)]
M = [[jorbar_cols()[c][r] for c in range(16)] for r in range(4)]
print("rank of overline{o} (Jordan map of M_2(F_3)):", rank(M), "-> onto:", rank(M)==4, ", dim ker =", 16-rank(M))
a = E[(0,1)]
def D(x): return add(mul(a,x), neg(mul(x,a)))
allm = [(r,c,d,e) for r in range(p) for c in range(p) for d in range(p) for e in range(p)]
# 1) Delta == 0 on all pairs (so the hypothesis 'vanishes on the sigma-zero pairs' holds)
worst = None
for x in allm:
    for y in allm:
        d = add(D(jor(x,y)), neg(add(jor(D(x),y), jor(x,D(y)))))
        if d != (0,0,0,0): worst=(x,y,d); break
    if worst: break
print("Leibniz defect identically zero:", worst is None)
# 2) D is a braided-symmetric derivation (same statement, restated)
print("D is a derivation of (A, o):", worst is None)
# 3) uniqueness of the factor S of the defect: overline{o} onto => S = 0
print("factor S of the defect is S = 0 (unique since o is onto)")
# 4) does S agree with D on the products?
x,y = E[(1,0)], E[(0,0)]          # e21, e11
print("x o y =", jor(x,y), " D(x o y) =", D(jor(x,y)), " S(x o y) = (0,0,0,0)")
print("S agrees with D on the products:", D(jor(x,y))==(0,0,0,0))
# 5) but the Jordan product map is not identically killed by D
cnt = sum(1 for u in allm for v in allm if D(jor(u,v))!=(0,0,0,0))
print("pairs (x,y) with D(x o y) != 0:", cnt, "of", len(allm)**2)
