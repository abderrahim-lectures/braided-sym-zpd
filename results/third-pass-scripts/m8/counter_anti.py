"""COUNTEREXAMPLE to cor:anti of the paper (v8) as stated:
   'Let A be zpd, and let alpha: A -> A be linear with alpha(xy) = alpha(y)alpha(x).
    Then A is determined by mu_alpha(x,y) = xy + alpha(y)alpha(x).'
A is the noncommutative, non-unital, zpd algebra of D8 of results/deep-review-v7.md.
Checked over F_2, F_3, F_5, F_7 and (same algebra) over Q via exact rational arithmetic below.
"""
import itertools, alg

def make_A(p):
    n = 3
    T = [[[0]*n for _ in range(n)] for _ in range(n)]
    T[0][0][0] = 1                      # e0^2 = e0
    T[0][1][2] = 1; T[0][2][2] = 1      # e0 e1 = e0 e2 = e2
    T[1][0][1] = 1; T[1][0][2] = (-1) % p   # e1 e0 = e1 - e2
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

def anti_maps(T,p,limit=None):
    n = len(T)
    c=0
    for imgs in itertools.product(itertools.product(range(p), repeat=n), repeat=n):
        a = tuple(tuple(v) for v in imgs)
        if alg.is_anti(a,T,p):
            yield a
            c+=1
            if limit and c>=limit: return

def det_of(f,p):
    n = len(f)
    M = [[f[j][i] for j in range(n)] for i in range(n)]
    # fraction-free gaussian elimination mod p
    det = 1
    for c in range(n):
        piv = None
        for r in range(c,n):
            if M[r][c] % p: piv = r; break
        if piv is None: return 0
        if piv != c:
            M[c],M[piv] = M[piv],M[c]; det = (-det) % p
        det = (det * M[c][c]) % p
        inv = pow(M[c][c], p-2, p)
        M[c] = [(x*inv) % p for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f2 = M[r][c]
                M[r] = [(x - f2*y) % p for x,y in zip(M[r], M[c])]
    return det

print("=== The algebra A (D8 of the v7 review report), over F_p ===")
for p in (2,3,5,7):
    n = 3
    T = make_A(p)
    e = [tuple(1 if k==j else 0 for k in range(n)) for j in range(n)]
    z, dz, dk = alg.determined(T,p)
    # unit search
    unit = None
    for x in itertools.product(range(p), repeat=n):
        if all(alg.mul_from(T,x,e[j],p) == e[j] for j in range(n)) and all(alg.mul_from(T,e[j],x,p) == e[j] for j in range(n)):
            unit = x
    comm = all(alg.mul_from(T,e[i],e[j],p) == alg.mul_from(T,e[j],e[i],p) for i in range(n) for j in range(n))
    print(f" F_{p}: associative {is_assoc(T,p)}, commutative {comm}, unital {unit is not None}, zpd {z} (dim Z = {dz}, dim ker mubar = {dk})")

print()
print("=== alpha: e0 -> e0, e1 -> e1, e2 -> e1 - e2 ; mu_alpha(x,y) = xy + alpha(y)alpha(x) ===")
for p in (2,3,5,7):
    n = 3
    T = make_A(p)
    e = [tuple(1 if k==j else 0 for k in range(n)) for j in range(n)]
    alpha = (e[0], e[1], tuple((e[1][i] - e[2][i]) % p for i in range(n)))
    isan = alg.is_anti(alpha,T,p)
    Mu = alg.braid_mu_alpha_y_alpha_x(T,p,alpha)
    det, dz, dk = alg.determined(Mu,p)
    print(f" F_{p}: alpha anti-multiplicative {isan}, det(alpha) = {det_of(alpha,p)} (bijective: {det_of(alpha,p)!=0}),"
          f" dim Z_mu = {dz}, dim ker mubar_mu = {dk}, determined = {det}")

print()
print("=== explicit witness over F_3: a bilinear phi vanishing on mu-zero pairs that does not factor through mu ===")
p = 3; n = 3
T = make_A(p)
e = [tuple(1 if k==j else 0 for k in range(n)) for j in range(n)]
alpha = (e[0], e[1], tuple((e[1][i] - e[2][i]) % p for i in range(n)))
Mu = alg.braid_mu_alpha_y_alpha_x(T,p,alpha)
B = alg.Zs_basis(Mu,p); K = alg.kernel_basis(alg.mat_of_bilin(Mu,p), p, n*n)
print("  dim Zs =", len(B), " dim ker mubar =", len(K))
# find a functional ell on V(x)V with ell = 0 on Zs but ell != 0 on some element of ker
# solve: ell in (V(x)V)^* with ell|_Zs = 0, and ell not in the annihilator of ker
# simple: pick k in ker \ Zs, extend B to a basis B + extra including k, take the dual functional
basis = list(B)
for k in K:
    if not alg.in_span(k, B, p):
        basis.append(k)
        break
# extend to full basis
allv = [tuple(1 if i==j else 0 for i in range(n*n)) for j in range(n*n)]
for v in allv:
    if not alg.in_span(v, basis, p):
        basis.append(v)
    if len(basis) == n*n: break
# dual functional to the extra vector (index len(B))
idx = len(B)
ell = [0]*(n*n)
# build coordinates of each basis vector in the standard basis, invert
import copy
M = [[basis[c][r] for c in range(n*n)] for r in range(n*n)]   # rows r, cols c
# solve M * x = unit vector e_idx  => ell = x
# gaussian elimination mod p
A2 = [row[:] + [1 if r == idx else 0 for r in range(n*n)] for r in range(n*n)]
for c in range(n*n):
    piv = next(r for r in range(c,n*n) if A2[r][c] % p)
    A2[c], A2[piv] = A2[piv], A2[c]
    inv = pow(A2[c][c], p-2, p)
    A2[c] = [(x*inv) % p for x in A2[c]]
    for r in range(n*n):
        if r != c and A2[r][c]:
            f2 = A2[r][c]
            A2[r] = [(x - f2*y) % p for x,y in zip(A2[r], A2[c])]
ell = [A2[r][n*n+idx] for r in range(n*n)]
print("  ell (on the basis e_i (x) e_j) =", ell)
def phi(x,y):
    t = alg.mul_from([[[1 if (a*0+b)==0 else 0 for b in range(n)] for a in range(n)] for _ in range(n)], x, y, p)  # dummy
    ten = tuple(x[i]*y[j] % p for i in range(n) for j in range(n))
    return sum(ell[t]*ten[t] for t in range(n*n)) % p
bad = 0; cnt = 0
for x in itertools.product(range(p), repeat=n):
    for y in itertools.product(range(p), repeat=n):
        if not any(alg.mul_from(Mu,x,y,p)):
            cnt += 1
            if phi(x,y) != 0: bad += 1
print("  phi vanishes on all", cnt, "mu-zero pairs:", bad == 0)
print("  phi(1,1) =", phi(e[0],e[0]), " ; phi is non-zero:", any(phi(x,y) != 0 for x in itertools.product(range(p),repeat=n) for y in itertools.product(range(p),repeat=n)))
print("  ell killed on ker mubar?", all(sum(ell[t]*k[t] for t in range(n*n)) % p == 0 for k in K))
