"""COR:ANTI COUNTEREXAMPLE -- final, carefully verified.
A = <e0,e1,e2> over F_p:  e0^2 = e0,  e0 e1 = e0 e2 = e2,  e1 e0 = e1 - e2,  all else 0.
A is associative, noncommutative, NON-UNITAL, and zpd (dim Z = dim ker mbar = 6).
alpha anti-multiplicative, even bijective; mu_alpha(x,y) = xy + alpha(y)alpha(x) = (id+alpha)(xy).
Then A is NOT determined by mu_alpha.  An explicit bilinear phi vanishes on every mu-zero
pair and takes different values on two pairs with the same mu-value, so no psi with phi = psi o mu.
"""
import itertools, alg

def make_A(p):
    n = 3
    T = [[[0]*n for _ in range(n)] for _ in range(n)]
    T[0][0][0] = 1
    T[0][1][2] = 1; T[0][2][2] = 1
    T[1][0][1] = 1; T[1][0][2] = (-1) % p
    return T

def is_assoc(T,p):
    n = len(T)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                a = alg.mul_from(T, T[i][j], tuple(1 if s==k else 0 for s in range(n)), p)
                b = alg.mul_from(T, tuple(1 if s==i else 0 for s in range(n)), T[j][k], p)
                if a != b: return False
    return True

def E(p,n): return [tuple(1 if k==j else 0 for k in range(n)) for j in range(n)]

def analyse(p, alpha_spec, label):
    n = 3
    T = make_A(p); e = E(p,n)
    alpha = tuple(tuple(alpha_spec[j][i] % p for i in range(n)) for j in range(n))
    Mu = alg.braid_mu_alpha_y_alpha_x(T,p,alpha)
    det, dz, dk = alg.determined(Mu,p)
    print(f"[{label}] p={p}: alpha anti-mult={alg.is_anti(alpha,T,p)}, alpha(e0)={alpha[0]}, alpha(e1)={alpha[1]}, alpha(e2)={alpha[2]}")
    print(f"    A zpd={alg.determined(T,p)[0]}, mu_alpha: dim Z_mu = {dz}, dim ker mubar_mu = {dk}, determined = {det}")
    if det: return None
    # explicit phi: functional ell vanishing on Zs_mu but not on ker mu
    B = alg.Zs_basis(Mu,p)
    K = alg.kernel_basis(alg.mat_of_bilin(Mu,p), p, n*n)
    ann = alg.kernel_basis(B, p, n*n)                  # ell with ell . b = 0 for b in Zs
    ell = None
    for L in ann:
        if any(sum(L[t]*k[t] for t in range(n*n)) % p for k in K):
            ell = L; break
    assert ell is not None
    def phi(x,y):
        ten = tuple(x[i]*y[j] % p for i in range(n) for j in range(n))
        return sum(ell[t]*ten[t] for t in range(n*n)) % p
    # verify phi vanishes on mu-zero pairs and find two pairs with equal mu, different phi
    zero_ok = True
    pts = list(itertools.product(range(p), repeat=n))
    for x in pts:
        for y in pts:
            if not any(alg.mul_from(Mu,x,y,p)) and phi(x,y) != 0:
                zero_ok = False
    bymu = {}
    clash = None
    for x in pts:
        for y in pts:
            key = alg.mul_from(Mu,x,y,p)
            if key in bymu and phi(*bymu[key]) != phi(x,y) and clash is None:
                clash = (bymu[key], (x,y), key)
            bymu.setdefault(key, (x,y))
    print(f"    phi = ell . (x (x) y) with ell = {ell}")
    print(f"    phi vanishes on every mu-zero pair: {zero_ok}")
    if clash:
        (x1,y1),(x2,y2),key = clash
        print(f"    mu({x1},{y1}) = {key} = mu({x2},{y2}), but phi = {phi(x1,y1)} vs {phi(x2,y2)}: phi does NOT factor through mu")
    return alpha

print("=== the algebra ===")
for p in (2,3,5,7):
    n=3; T = make_A(p); e = E(p,n)
    unit = [x for x in itertools.product(range(p),repeat=n)
            if all(alg.mul_from(T,x,e[j],p)==e[j] for j in range(n)) and all(alg.mul_from(T,e[j],x,p)==e[j] for j in range(n))]
    comm = all(alg.mul_from(T,e[i],e[j],p)==alg.mul_from(T,e[j],e[i],p) for i in range(n) for j in range(n))
    z,dz,dk = alg.determined(T,p)
    print(f"  F_{p}: associative={is_assoc(T,p)} commutative={comm} unital={bool(unit)} zpd={z} (dim Z={dz}, dim ker={dk})")

print()
print("=== counterexamples to cor:anti ===")
# char != 2 : alpha(e0)=e0, alpha(e1)=e1, alpha(e2)=e1-e2
for p in (3,5,7):
    analyse(p, [[1,0,0],[0,1,0],[0,1,-1]], "uniform alpha, p odd")
# char 2 : alpha(e0)=e0+e2, alpha(e1)=e1, alpha(e2)=e1+e2
analyse(2, [[1,0,1],[0,1,0],[0,1,1]], "alpha for p=2")
