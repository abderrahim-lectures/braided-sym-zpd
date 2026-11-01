#!/usr/bin/env python3
"""
m1 audit (swarm smvxd25ff), second script: the individual claims tied to
cor:twisted / cor:anti and to the twisted-braiding sentences of the paper.

Convention.  e_0,...,e_{n-1} basis of A over F_p, T[i,j,k] = coefficient of e_k in
e_i e_j, and C is the matrix of the linear map alpha: alpha(e_i) = sum_l C[i,l] e_l.
The paper's twisted product (line 134/136: sigma(x (x) y) = alpha(y) (x) alpha(x)) is

        mu_alpha(x,y) = xy + alpha(y) alpha(x),

which is what `mu_table` computes.  For a COMMUTATIVE A the two orders agree, so the
search of the first script (commutative algebras only) is not affected by the order.

Self-tests at the end of the file pin down the implementation.
"""
import itertools
import numpy as np

np.set_printoptions(linewidth=200)


# ---------------------------------------------------------------- linear algebra over F_p
def gauss(rows, ncols, p):
    basis = []
    for r in rows:
        v = np.asarray(r, dtype=np.int64).copy() % p
        for b, piv in basis:
            c = v[piv] % p
            if c:
                v = (v - c * b) % p
        nz = np.nonzero(v)[0]
        if nz.size:
            piv = int(nz[0])
            v = (v * pow(int(v[piv]), -1, p)) % p
            basis.append((v, piv))
    return len(basis)


def all_vecs(p, n):
    return np.array(list(itertools.product(range(p), repeat=n)), dtype=np.int64)


def mbar(Tm, p):
    """matrix of mu_bar: A (x) A -> A, x (x) y |-> mu(x,y); row k, column i*n+j."""
    n = Tm.shape[0]
    return np.transpose(Tm, (2, 0, 1)).reshape(n, n * n) % p


def kerdim(Tm, p):
    n = Tm.shape[0]
    return n * n - gauss([mbar(Tm, p)[k] for k in range(n)], n * n, p)


def zsdim(Tm, p, vecs):
    n = Tm.shape[0]
    P = np.einsum('ai,bj,ijk->abk', vecs, vecs, Tm) % p
    zero = (P == 0).all(axis=2)
    seen, rows = set(), []
    for a, b in zip(*np.nonzero(zero)):
        v = np.kron(vecs[a], vecs[b]) % p
        key = v.tobytes()
        if key not in seen:
            seen.add(key)
            rows.append(v)
    return gauss(rows, n * n, p), int(zero.sum())


def determined(Tm, p, vecs):
    return zsdim(Tm, p, vecs)[0] == kerdim(Tm, p)


def mu_table(T, p, C=None):
    """T + (y,x) |-> alpha(y) alpha(x)   (i.e. mu(x,y) = xy + alpha(y)alpha(x))."""
    if C is None:
        return T % p
    return (T + np.einsum('jl,im,lmk->ijk', C, C, T)) % p


def f_table(T, p, C):
    """table of (x,y) |-> f(xy) for the linear map f with matrix C."""
    return np.einsum('iml,lk->imk', T, C) % p


def unital(T, p):
    n = T.shape[0]
    for u in all_vecs(p, n):
        if all(np.array_equal((np.einsum('i,ijk->jk', u, T) % p)[j], np.eye(n, dtype=np.int64)[j])
               for j in range(n)):
            return u
    return None


def endomorphisms(T, p):
    n = T.shape[0]
    out = []
    for code in range(p ** (n * n)):
        v, C = code, np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for l in range(n):
                C[i, l] = v % p
                v //= p
        if np.array_equal(np.einsum('il,jm,lmk->ijk', C, C, T) % p,
                          np.einsum('ijk,kl->ijl', T, C) % p):
            out.append(C)
    return out


def commutative_algebras(p, n):
    pairs = [(i, j) for i in range(n) for j in range(i, n)]
    block = p ** n
    for code in range(block ** len(pairs)):
        c, T = code, np.zeros((n, n, n), dtype=np.int64)
        for (i, j) in pairs:
            w = c % block
            c //= block
            vec = np.zeros(n, dtype=np.int64)
            for k in range(n):
                vec[k] = w % p
                w //= p
            T[i, j] = vec
            T[j, i] = vec
        yield T


def matrix_units(n, p):
    T = np.zeros((n * n, n * n, n * n), dtype=np.int64)
    ix = lambda i, j: i * n + j
    for i in range(n):
        for j in range(n):
            for k in range(n):
                T[ix(i, j), ix(j, k), ix(i, k)] = 1
    return T


def conj_matrix(n, p, D):
    ix = lambda i, j: i * n + j
    C = np.zeros((n * n, n * n), dtype=np.int64)
    for i in range(n):
        for j in range(n):
            C[ix(i, j), ix(i, j)] = (D[i] * pow(int(D[j]), -1, p)) % p
    return C


def star(Tm, x, y, p):
    return np.einsum('i,j,ijk->k', x, y, Tm) % p


print("=== SELF-TESTS ===")
for (p, n, alpha_is_id, want) in [(3, 2, True, "Jordan"), (3, 2, "zero", "product")]:
    T = matrix_units(n, p)
    C = None if alpha_is_id == "zero" else np.eye(n * n, dtype=np.int64)
    Tm = mu_table(T, p, C)
    if want == "Jordan":
        ok = all(np.array_equal(star(Tm, e, f, p),
                                (star(T, e, f, p) + star(T, f, e, p)) % p)
                 for e in all_vecs(p, n * n) for f in all_vecs(p, n * n))
        print(f"  alpha = id on M_2(F_3): mu = Jordan product? {ok}")
    else:
        ok = all(np.array_equal(star(Tm, e, f, p), star(T, e, f, p))
                 for e in all_vecs(p, n * n) for f in all_vecs(p, n * n))
        print(f"  alpha = 0 on M_2(F_3): mu = product? {ok}")

p, n = 3, 2
Tdual = np.zeros((2, 2, 2), dtype=np.int64); Tdual[0, 0, 0] = 1; Tdual[0, 1, 1] = 1; Tdual[1, 0, 1] = 1
Cadual = np.array([[1, 0], [0, -1]]) % p                       # alpha(a + b eps) = a - b eps
Tmdual = mu_table(Tdual, p, Cadual)
vecs = all_vecs(p, 2)
print(f"  dual numbers over F_3, alpha(a+b eps)=a-b eps: mu = f(xy) with f = id+alpha? "
      f"{np.array_equal(Tmdual, f_table(Tdual, p, (np.eye(2,dtype=np.int64)+Cadual)%p))}")
print(f"    dim ker mu_bar = {kerdim(Tmdual,p)}, dim Zs = {zsdim(Tmdual,p,vecs)[0]} -> determined "
      f"{determined(Tmdual,p,vecs)} (paper ex:dual says: determined, not zpd: {not determined(Tdual,p,vecs)})")

print()
print("=== C1: 'commutativity alone is not enough' (tex 149 and 316) ===")
for p in (2, 3, 5):
    n = 2
    T = np.zeros((n, n, n), dtype=np.int64); T[0, 0, 0] = 1; T[1, 1, 1] = 1     # K x K
    C = np.array([[1, 0], [1, 0]])          # alpha(e0) = e0, alpha(e1) = e0  <=> alpha(a,b) = (a+b,0)
    Tm = mu_table(T, p, C)
    vecs = all_vecs(p, n)
    e1, one = np.array([0, 1]), np.array([1, 1])
    print(f"  F_{p}: alpha multiplicative? "
          f"{np.array_equal(np.einsum('il,jm,lmk->ijk',C,C,T)%p, np.einsum('ijk,kl->ijl',T,C)%p)}"
          f";  e1.e1 = {star(T,e1,e1,p)}, e1.1 = {star(T,e1,one,p)}")
    print(f"        mu(e1,e1) = {star(Tm,e1,e1,p)}, mu(e1,1) = {star(Tm,e1,one,p)}  -> equal products, different mu: "
          f"{not np.array_equal(star(Tm,e1,e1,p), star(Tm,e1,one,p))}")
    print(f"        A is zpd: {determined(T,p,vecs)}; dim ker mu_bar = {kerdim(Tm,p)}, Zs = "
          f"{zsdim(Tm,p,vecs)[0]} -> determined by mu_alpha: {determined(Tm,p,vecs)}")

print()
print("=== C2: sigma^2 = alpha^2 (x) alpha^2 -> sigma involutive iff alpha^2 = id ===")
def sig(v, n, C, p):
    X = v.reshape(n, n)                       # X[i,j] coefficient of e_i (x) e_j
    return (C.T @ X @ C).reshape(n * n) % p   # sum X[i,j] alpha(e_j) (x) alpha(e_i)
for (p, n) in [(3, 2), (5, 3)]:
    for _ in range(3):
        C = np.random.default_rng(abs(p * n + _)).integers(0, p, (n, n))
        v = np.random.default_rng(n + _).integers(0, p, n * n)
        lhs = sig(sig(v, n, C, p), n, C, p)
        X = v.reshape(n, n)
        rhs = np.einsum('ij,ia,jb->ab', X, C.T @ C, C.T @ C).reshape(n * n) % p
        # alpha^2(x) (x) alpha^2(y) with x = sum X[i,j] ...; check on pure tensors instead:
        x, y = np.eye(n, dtype=np.int64)[0], np.eye(n, dtype=np.int64)[1]
        lhs2 = sig(sig(np.kron(x, y), n, C, p), n, C, p)
        rhs2 = np.kron(C.T @ C @ x, C.T @ C @ y) % p
        print(f"  F_{p} n={n}: sigma^2(x(x)y) = alpha^2 x (x) alpha^2 y ? {np.array_equal(lhs2, rhs2)}")

print()
print("=== C3: associativity of the twisted product (M_2(F_3), alpha = conj diag(1,-1)) ===")
p, n = 3, 2
T = matrix_units(n, p)
C = conj_matrix(n, p, np.array([1, -1]) % p)
Tm = mu_table(T, p, C)
print("  alpha matrix (diagonal in matrix units):", np.diag(C).tolist())
rng = np.random.default_rng(1)
found = None
for _ in range(50000):
    x, y, z = (rng.integers(0, p, n * n) for _ in range(3))
    if not np.array_equal(star(Tm, star(Tm, x, y, p), z, p), star(Tm, x, star(Tm, y, z, p), p)):
        found = (x, y, z); break
print("  non-associative triple:", found)
if found:
    x, y, z = found
    print("    (x*y)*z =", star(Tm, star(Tm, x, y, p), z, p), "  x*(y*z) =", star(Tm, x, star(Tm, y, z, p), p))
vecs4 = all_vecs(p, n * n)
print(f"  dim ker mu_bar = {kerdim(Tm,p)}, dim Zs = {zsdim(Tm,p,vecs4)[0]} -> determined: {determined(Tm,p,vecs4)}")

print()
print("=== C4: is mu_alpha of the form f(xy)? (M_2(F_3), alpha = conj diag(1,-1)) ===")
Mm, Mmu = mbar(T, p), mbar(Tm, p)
rM = gauss([Mm[k] for k in range(n * n)], n * n * n * n, p)
rBoth = gauss([Mm[k] for k in range(n * n)] + [Mmu[k] for k in range(n * n)], n * n * n * n, p)
print(f"  rank m_bar = {rM} (must be 4 = dim M_2(F_3)), rank mu_bar = "
      f"{gauss([Mmu[k] for k in range(n*n)], n*n*n*n, p)}")
print(f"  rank [m_bar; mu_bar] = {rBoth};  ker m_bar <= ker mu_bar (would mean mu = f o product): {rBoth == rM}")

print()
print("=== C5: is the 'unital' hypothesis of thm:zpd-fxy redundant? (F_2, dim 2,3) ===")
for (p, n) in [(2, 2), (2, 3)]:
    vecs = all_vecs(p, n)
    hits = []
    for T in commutative_algebras(p, n):
        if unital(T, p) is not None or not determined(T, p, vecs):
            continue
        for C in [m for m in np.array(list(itertools.product(range(p), repeat=n * n))).reshape(-1, n, n)]:
            if not determined(f_table(T, p, C), p, vecs):
                hits.append((T.copy(), C.copy())); break
        if len(hits) >= 2:
            break
    print(f"  F_{p} dim {n}: zpd non-unital A and linear f with A NOT determined by f(xy): {len(hits)}")
    for (T, C) in hits[:1]:
        Tf = f_table(T, p, C)
        print("    table T[i][j] (rows i, columns j, entries the vector e_i e_j):",
              [["".join(str(int(T[i, j, k])) for k in range(n)) for j in range(n)] for i in range(n)])
        print("    f (columns = images of e_i):", C.T.tolist(),
              f" dim ker mu_bar = {kerdim(Tf,p)}, dim Zs = {zsdim(Tf,p,vecs)[0]}")
