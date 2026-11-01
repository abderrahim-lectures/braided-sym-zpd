"""Independent exact verification over Q (sympy) of the cor:anti counterexample."""
from sympy import Matrix, Rational, symbols, simplify
import random
# A over Q, basis e0,e1,e2: e0^2=e0, e0e1=e0e2=e2, e1e0=e1-e2, all other products 0
def mul(u,v): return (u[0]*v[0], u[1]*v[0], u[0]*(v[1]+v[2]) - u[1]*v[0])
e=[(1,0,0),(0,1,0),(0,0,1)]
random.seed(1)
for _ in range(300):
    u=tuple(Rational(random.randint(-3,3)) for _ in range(3))
    v=tuple(Rational(random.randint(-3,3)) for _ in range(3))
    w=tuple(Rational(random.randint(-3,3)) for _ in range(3))
    assert mul(mul(u,v),w)==mul(u,mul(v,w))
print("A associative over Q (300 random rational triples)")
def ten(x,y):
    out=[0]*9
    for i in range(3):
        for j in range(3): out[i*3+j]=x[i]*y[j]
    return out
M = Matrix(3,9, lambda k,c: mul(e[c//3], e[c%3])[k])
print("rank mbar =", M.rank(), " dim ker mbar =", 9-M.rank())
# Z = span of x(x)y with xy=0.  Exact case analysis: xy=0 <=> x0y0=0, x1y0=0, x0(y1+y2)-x1y0=0.
# generators: x=e2 (all y); x,y in span{e1,e2}; y=e1-e2 (all x).
gens=[]
for v in e: gens.append(ten(e[2],v))
for x in (e[1],e[2]):
    for y in (e[1],e[2]): gens.append(ten(x,y))
for u in e: gens.append(ten(u,(0,1,-1)))
G = Matrix(gens).T
print("dim Z (zero-product tensors) =", G.rank())
print("Z subset ker mbar:", all((M*g).is_zero_matrix for g in [Matrix(gens).T]) )
al=[(1,0,0),(0,1,0),(0,1,-1)]
def lin(f,x): return tuple(sum(x[j]*f[j][i] for j in range(3)) for i in range(3))
print("alpha anti-multiplicative (basis pairs):", all(lin(al,mul(e[i],e[j]))==mul(lin(al,e[j]),lin(al,e[i])) for i in range(3) for j in range(3)))
# check anti-multiplicativity on random rational pairs too
ok=True
for _ in range(300):
    u=tuple(Rational(random.randint(-3,3)) for _ in range(3)); v=tuple(Rational(random.randint(-3,3)) for _ in range(3))
    if lin(al,mul(u,v))!=mul(lin(al,v),lin(al,u)): ok=False
print("alpha anti-multiplicative (300 random pairs):", ok)
print("alpha invertible, det =", Matrix(3,3,lambda i,j: al[j][i]).det())
def mu(u,v):
    a=mul(u,v); b=lin(al,a); return tuple(a[i]+b[i] for i in range(3))
Mu = Matrix(3,9, lambda k,c: mu(e[c//3], e[c%3])[k])
print("rank mubar_mu =", Mu.rank(), " dim ker mubar_mu =", 9-Mu.rank())
x0,x1,x2,y0,y1,y2 = symbols('x0 x1 x2 y0 y1 y2')
X=(x0,x1,x2); Y=(y0,y1,y2); mm=mul(X,Y)
print("mu(x,y) =", [simplify(c) for c in tuple(mm[i]+lin(al,mm)[i] for i in range(3))])
# Z_mu generators: mu=0 <=> x0y0=0 and x0(y1+y2)+x1y0=0, so x=e2 (all y), x,y in span{e1,e2}, y=e1-e2 (all x)
gens2=[]
for v in e: gens2.append(ten(e[2],v))
for x in (e[1],e[2]):
    for y in (e[1],e[2]): gens2.append(ten(x,y))
for u in e: gens2.append(ten(u,(0,1,-1)))
Gm=Matrix(gens2).T
print("dim Z_mu =", Gm.rank(), " (< 7 = dim ker mubar_mu  =>  NOT determined)")
print("witness: mu(e1,e0) =", mu(e[1],e[0]), "= mu(e0,e2) =", mu(e[0],e[2]),
      "; phi(x,y)=x0(y1+y2): phi(e1,e0) =", e[1][0]*(e[0][1]+e[0][2]), ", phi(e0,e2) =", e[0][0]*(e[2][1]+e[2][2]))
