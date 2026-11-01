"""Check the v8 Introduction annotation: on A = K x K (zpd), alpha(x,y)=(x+y,0) linear,
the pairs (e1,e1) and (e1,1) 'have the same product but different mu'."""
def test(p):
    def add(u,v): return tuple((a+b)%p for a,b in zip(u,v))
    def mul(u,v): return (u[0]*v[0]%p, u[1]*v[1]%p)
    alpha = lambda v: ((v[0]+v[1])%p, 0)
    one=(1%p,1%p); e1=(1%p,0)
    def mu(x,y): return add(mul(x,y), mul(alpha(y),alpha(x)))
    print("p =",p)
    print("  pair (e1,e1): product", mul(e1,e1), "mu", mu(e1,e1))
    print("  pair (e1, 1): product", mul(e1,one), "mu", mu(e1,one))
    print("  annotation's example works?", mu(e1,e1) != mu(e1,one))
    # find a genuine pair: same product as (1,1), different mu
    target = mul(one,one)
    found=[]
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    x=(a,b); y=(c,d)
                    if mul(x,y)==target and mu(x,y)!=mu(one,one):
                        found.append((x,y,mu(x,y)))
    print("  mu(1,1) =", mu(one,one), "; pairs with product 1 and different mu:", found[:3])
for p in (3,5,7):
    test(p)
