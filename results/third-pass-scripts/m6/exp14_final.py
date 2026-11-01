"""Experiment 14.
(A) paper's prop:matrix and line 413 re-derived by an independent algorithm
    (counts of zero pairs + ranks + span dimensions); also the ordinary product.
(B) ex:dual: image of the twisted product is 1-dimensional, and an explicit linear D
    that satisfies the hypothesis of rem:derivations but is NOT a braided-symmetric
    derivation  -> the abstract's "hence derivations can be studied through zero products"
    is not licensed.
(C) a linear involution sigma on A(x)A for A = F_p^2 (zpd) for which (A, mu_sigma) is NOT
    determined, checked over two/three fields with the same integer matrix.
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *
from exp10_sigma import mu_from_sigma, mat_mul_np


def paper_matrix(p=3):
    n = 4  # basis E11,E12,E21,E22 -> index i*2+j
    A = alg_matrix_units(2, p)
    alpha = [[0] * n for _ in range(n)]   # conjugation by diag(1,-1)
    # E11->E11, E12->-E12, E21->-E21, E22->E22
    alpha[0][0] = 1
    alpha[1][1] = p - 1
    alpha[2][2] = p - 1
    alpha[3][3] = 1
    def mu(x, y):
        xy = multiply(n, A, x, y, p)
        yx = multiply(n, A, y, x, p)
        ayx = [sum(yx[i] * alpha[i][j] for i in range(n)) % p for j in range(n)]
        return [(u + v) % p for u, v in zip(xy, ayx)], xy
    elems = list(product(range(p), repeat=n))
    zpairs = 0
    MU = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            e = [0] * n; e[i] = 1
            f = [0] * n; f[j] = 1
            MU[i][j] = mu(e, f)[0]
    U = mu_matrix(n, MU)
    r = rank(U, p, n * n)
    dimker = n * n - r
    gens = []
    for x in elems:
        for y in elems:
            if not any(mu(x, y)[0]):
                zpairs += 1
                t = [0] * (n * n)
                for i in range(n):
                    if x[i]:
                        for j in range(n):
                            if y[j]:
                                t[i * n + j] = (x[i] * y[j]) % p
                gens.append(t)
    dimZ = rank(gens, p, n * n)
    print(f"(A) M_2(F_{p}), alpha = conj diag(1,-1), mu = xy + alpha(yx) = xy + alpha(y)alpha(x):")
    print(f"    zero pairs = {zpairs}, rank mu-bar = {r}, dim ker = {dimker}, dim Z_mu = {dimZ}, "
          f"determined = {dimZ == dimker}")
    # ordinary product
    MUo = product_mu(n, A)
    Uo = mu_matrix(n, MUo)
    ro = rank(Uo, p, n * n)
    genso = []
    cnto = 0
    for x in elems:
        for y in elems:
            if not any(multiply(n, A, x, y, p)):
                cnto += 1
                t = [0] * (n * n)
                for i in range(n):
                    if x[i]:
                        for j in range(n):
                            if y[j]:
                                t[i * n + j] = (x[i] * y[j]) % p
                genso.append(t)
    print(f"    ordinary product: zero pairs = {cnto}, rank = {ro}, dim ker = {n*n-ro}, "
          f"dim Z = {rank(genso, p, n*n)}")
    # transpose braiding: mu(x,y) = x y + y^T x^T
    def muT(x, y):
        def tmat(v):
            return [[v[0], v[2]], [v[1], v[3]]]
        X, Y = tmat(x), tmat(y)
        XY = [[sum(X[i][k] * Y[k][j] for k in range(2)) % p for j in range(2)] for i in range(2)]
        Yt = [[Y[j][i] for j in range(2)] for i in range(2)]
        Xt = [[X[j][i] for j in range(2)] for i in range(2)]
        YtXt = [[sum(Yt[i][k] * Xt[k][j] for k in range(2)) % p for j in range(2)] for i in range(2)]
        flat = lambda M: [M[0][0], M[0][1], M[1][0], M[1][1]]
        return [(u + v) % p for u, v in zip(flat(XY), flat(YtXt))]
    MUT = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            e = [0] * n; e[i] = 1
            f = [0] * n; f[j] = 1
            MUT[i][j] = muT(e, f)
    UT = mu_matrix(n, MUT)
    rT = rank(UT, p, n * n)
    gT = []
    cntT = 0
    for x in elems:
        for y in elems:
            if not any(muT(x, y)):
                cntT += 1
                t = [0] * (n * n)
                for i in range(n):
                    if x[i]:
                        for j in range(n):
                            if y[j]:
                                t[i * n + j] = (x[i] * y[j]) % p
                gT.append(t)
    print(f"    transpose braiding xy + y^T x^T: zero pairs = {cntT}, rank = {rT}, "
          f"dim ker = {n*n-rT}, dim Z = {rank(gT, p, n*n)}")


def dual_witness(p=5):
    """ex:dual: mu_alpha has 1-dimensional image; find D satisfying rem:derivations'
    hypothesis which is not a braided-symmetric derivation."""
    n = 2
    A = alg_dual_numbers(p)
    alpha = [[1, 0], [0, p - 1]]   # a + b eps -> a - b eps
    def mu(x, y):
        xy = multiply(n, A, x, y, p)
        yx = multiply(n, A, y, x, p)
        ayx = [sum(yx[i] * alpha[i][j] for i in range(n)) % p for j in range(n)]
        return [(u + v) % p for u, v in zip(xy, ayx)]
    elems = list(product(range(p), repeat=n))
    Im = set()
    for x in elems:
        for y in elems:
            Im.add(tuple(mu(x, y)))
    print(f"(B) dual numbers over F_{p}: |image of mu_alpha| = {len(Im)}, image span = {sorted(Im)}")
    # D: a + b eps -> b (i.e. D(eps) = 1, D(1) = 0)
    D = lambda v: (v[1], 0)
    zero_pairs = [(x, y) for x in elems for y in elems if not any(mu(x, y))]
    ok = all(not any([(u + v) % p for u, v in zip(mu(D(x), y), mu(x, D(y)))]) for x, y in zero_pairs)
    print(f"    D(a+b eps) = b : hypothesis of rem:derivations holds on all {len(zero_pairs)} "
          f"mu-zero pairs? {ok}")
    # is D a braided-symmetric derivation?
    bad = None
    for x in elems:
        for y in elems:
            lhs = D(mu(x, y))
            rhs = [(u + v) % p for u, v in zip(mu(D(x), y), mu(x, D(y)))]
            if lhs != rhs:
                bad = (x, y, lhs, rhs)
                break
        if bad:
            break
    print(f"    D a braided-symmetric derivation? {bad is None}   witness: {bad}")
    # S = D on span of products?  span of products = K*1
    print(f"    span of products of mu_alpha: {sorted(set(tuple(mu(x, y)) for x in elems for y in elems))}")


def sigma_example():
    """(C) an involution sigma (integer matrix) on A(x)A, A = K^2, with the product
    mu_sigma = m(1+sigma) NOT determined over F_2, F_3, F_5."""
    N = 4
    # candidate found in the F_2 scan
    cand = [[0, 0, 0, 1], [0, 0, 1, 1], [1, 1, 0, 0], [1, 0, 0, 0]]
    for p in (2, 3, 5, 7):
        S2 = mat_mul_np(cand, cand, N, p)
        is_inv = all(S2[i][j] == (1 if i == j else 0) for i in range(N) for j in range(N))
        A = alg_diagonal(2, p)
        MU = mu_from_sigma(2, A, cand, p)
        d = determined(2, MU, p)
        print(f"(C) p={p}: sigma^2 = id? {is_inv}; A = K^2 zpd = "
              f"{determined(2, A, p)[0]==determined(2, A, p)[1]}; (A, mu_sigma): "
              f"dimZ={d[0]} dimker={d[1]} determined={d[0]==d[1]}")
    print("    sigma =", cand)


if __name__ == '__main__':
    paper_matrix(3)
    print()
    dual_witness(5)
    print()
    sigma_example()
