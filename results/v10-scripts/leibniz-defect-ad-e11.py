# Certificate for the v9 claim in the abstract (l.110) and Introduction (l.159):
#   "the Leibniz defect D(x.s y) - D(x).s y - x.s D(y) ... factors through the product,
#    and D is a braided-symmetric derivation exactly when the factor agrees with D on the products"
# Assemble: A = M_2(F_3), sigma = swap  (x.s y = xy+yx), D = ad_{e11}.
p = 3
def add(u,v): return tuple((a+b) % p for a,b in zip(u,v))
def neg(u):   return tuple((-a) % p for a in u)
def sub(u,v): return add(u,neg(v))
def mul(u,v):
    a,b,c,d = u; e,f,g,h = v
    return ((a*e+b*g) % p, (a*f+b*h) % p, (c*e+d*g) % p, (c*f+d*h) % p)
def scal(k,u): return tuple((k*a) % p for a in u)
ZERO = (0,0,0,0)
A = [(a,b,c,d) for a in range(p) for b in range(p) for c in range(p) for d in range(p)]
assert len(A) == 81
def jor(x,y): return add(mul(x,y), mul(y,x))          # sigma = swap
g = (1,0,0,0)                                          # g = e_11
def D(x):    return sub(mul(g,x), mul(x,g))            # inner derivation ad_g

# --- 0. D is a derivation, hence a Jordan (= braided-symmetric for the swap) derivation
der_ok = all(D(mul(x,y)) == add(mul(D(x),y), mul(x,D(y))) for x in A for y in A)
bsd_ok = all(D(jor(x,y))== add(jor(D(x),y), jor(x,D(y)))  for x in A for y in A)
print("D=ad_{e11} is a derivation:", der_ok, "| D is BSD for sigma=swap:", bsd_ok)

# --- 1. A is determined by mu_sigma = Jordan product: check the criterion dim Z = dim ker
basisA = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
def coords(z): return list(z)
def rank(vecs, ncol):
    M = [list(map(lambda t: t % p, v)) for v in vecs]
    r = 0; piv = []
    for c in range(ncol):
        pr = None
        for i in range(r, len(M)):
            if M[i][c] % p: pr = i; break
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p-2, p)
        M[r] = [(v*inv) % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(a - f*b) % p for a,b in zip(M[i], M[r])]
        piv.append(c); r += 1
    return r
# matrix of  overbar(jor): A(x)A -> A, in bases e_i (x) e_j
cols = []
for i in range(4):
    for j in range(4):
        cols.append(list(jor(basisA[i], basisA[j])))     # column = image of e_i (x) e_j
M = [[cols[j][i] for j in range(16)] for i in range(4)]
r = rank(M, 16)
print("rank of overbar(jor) =", r, "; dim ker =", 16-r)
zero_tensors = []
for x in A:
    for y in A:
        if jor(x,y) == ZERO:
            t = [0]*16
            for i in range(4):
                for j in range(4):
                    t[4*i+j] = (x[i]*y[j]) % p
            zero_tensors.append(t)
dz = rank(zero_tensors, 16)
print("number of Jordan-zero pairs:", len(zero_tensors), "; dim span{x(x)y : x.y=0} =", dz)
print("A=M_2(F_3) determined by the Jordan product:", dz == 16-r)

# --- 2. the Leibniz defect of D for the product ._sigma
def Phi(x,y):  return add(jor(D(x),y), jor(x,D(y)))          # RHS  (the "sum")
def Delta(x,y):return sub(D(jor(x,y)), Phi(x,y))             # Leibniz defect
print("Delta == 0 identically:", all(Delta(x,y)==ZERO for x in A for y in A))
print("pair with Jordan product 0 and Delta nonzero:",
      any(Delta(x,y)!=ZERO for x in A for y in A if jor(x,y)==ZERO))
print("Phi == 0 identically:", all(Phi(x,y)==ZERO for x in A for y in A))

# --- 3. factor of Delta through the product is T = 0 on im(overbar jor) = A (rank 4, char != 2)
print("im(overbar jor) = A:", r == 4)
T = {z: ZERO for z in A}                                      # Delta = T o (x,y)->x.y with T = 0
T_agrees_with_D = all(T[jor(x,y)] == D(jor(x,y)) for x in A for y in A)
print("factor T of Delta agrees with D on the products:", T_agrees_with_D)
x0, y0 = (1,0,0,0), (0,1,0,0)                                  # e11, e12
print("counter-pair: e11.e12 =", jor(x0,y0), " D(that) =", D(jor(x0,y0)), " T(that) =", T[jor(x0,y0)])
print("=> D is a BSD (True) but the factor of its defect does NOT agree with D on the products (False)")

# --- 4. what rem:derivations really gives: the factor S of Phi agrees with D on the products
S = {}
for z in A:
    for x in A:
        for y in A:
            if jor(x,y) == z: S[z] = Phi(x,y); break
        else: continue
        break
print("S well defined on im(overbar jor):", all(Phi(x,y)==S[jor(x,y)] for x in A for y in A))
print("S agrees with D on the products:", all(S[jor(x,y)]==D(jor(x,y)) for x in A for y in A))
