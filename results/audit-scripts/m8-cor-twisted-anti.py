#!/usr/bin/env python3
"""Positive checks for cor:twisted (4.4) and cor:anti (4.5) of
paper/braided-sym-zpd.tex, and for remark rem:inner's equivalence.

An algebra is given by a multiplication table on a basis over F_p; a linear map
alpha by its matrix.  For each mu we report dim ker(mu-bar) and dim Zs; the two
agree iff A is determined by mu (Bresar Prop 1.3).
"""
import itertools
import numpy as np


def rref_rank(rows, p):
    if not rows:
        return 0
    M = np.array(rows, dtype=np.int64) % p
    nr, nc = M.shape
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if M[i, c] % p), None)
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        M[r] = (M[r] * pow(int(M[r, c]) % p, p - 2, p)) % p
        for i in range(nr):
            if i != r and M[i, c] % p:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == nr:
            break
    return r


class Alg:
    def __init__(self, n, table, p):
        self.n, self.p = n, p
        # table[i][j] = list of n structure constants of e_i e_j
        self.t = [[[c % p for c in table[i][j]] for j in range(n)] for i in range(n)]

    def mul(self, x, y):
        out = [0] * self.n
        for i, xi in enumerate(x):
            if xi:
                for j, yj in enumerate(y):
                    if yj:
                        tij = self.t[i][j]
                        for k in range(self.n):
                            out[k] += xi * yj * tij[k]
        return [c % self.p for c in out]

    def lin(self, M, x):
        p = self.p
        return [sum(M[k][i] * x[i] for i in range(self.n)) % p for k in range(self.n)]


def analyse(name, A, mu):
    n, p = A.n, A.p
    cols = []
    for i in range(n):
        for j in range(n):
            ei = [0] * n
            ei[i] = 1
            ej = [0] * n
            ej[j] = 1
            cols.append(mu(ei, ej))
    rows = [[cols[c][k] for c in range(n * n)] for k in range(n)]
    dimker = n * n - rref_rank(rows, p)
    tens = []
    for x in itertools.product(range(p), repeat=n):
        for y in itertools.product(range(p), repeat=n):
            if not any(mu(list(x), list(y))):
                v = [0] * (n * n)
                for i in range(n):
                    for j in range(n):
                        v[i * n + j] = x[i] * y[j] % p
                tens.append(v)
    dimZs = rref_rank(tens, p)
    print(f"{name}: dim A = {n} over F_{p}, rank(mu-bar) = {n*n-dimker}, dim ker = {dimker}, "
          f"dim Zs = {dimZs} -> {'DETERMINED' if dimker == dimZs else 'NOT determined'}")


def main():
    p = 3
    # ---------------------------------------------------------------- F_p x F_p
    # basis e1=(1,0), e2=(0,1); componentwise product; alpha = swap
    tab_kk = [[[1, 0], [0, 0]], [[0, 0], [0, 1]]]
    A = Alg(2, tab_kk, p)
    print("== cor:twisted (4.4): A = F_3 x F_3 (commutative, zpd), alpha = swap ==")
    alpha = [[0, 1], [1, 0]]
    analyse("mu(x,y)=xy+alpha(y)alpha(x)", A, lambda x, y: [(a + b) % p for a, b in
            zip(A.mul(x, y), A.mul(A.lin(alpha, y), A.lin(alpha, x)))])
    print()

    # ---------------------------------------------------------------- T_2(F_p)
    # basis e11=(1,0,0), e12=(0,1,0), e22=(0,0,1)
    I, E12, J = [1, 0, 0], [0, 1, 0], [0, 0, 1]
    def prod(u, v):
        # (a E11 + b E12 + c E22)(a' E11 + b' E12 + c' E22)
        a, b, c = u
        a2, b2, c2 = v
        return [a * a2 % p, (a * b2 + b * c2) % p, c * c2 % p]
    tab_T = [[prod(u, v) for v in (I, E12, J)] for u in (I, E12, J)]
    T = Alg(3, tab_T, p)
    # alpha = J0 x^T J0 with J0 = antidiag(1,1) : anti-automorphism, E11<->E22, E12->E12
    alphaT = [[0, 0, 1], [0, 1, 0], [1, 0, 0]]
    print("== cor:anti (4.5): A = T_2(F_3) (unital zpd), alpha = flip anti-automorphism ==")
    analyse("mu(x,y)=xy+alpha(y)alpha(x)", T, lambda x, y: [(a + b) % p for a, b in
            zip(T.mul(x, y), T.mul(T.lin(alphaT, y), T.lin(alphaT, x)))])
    # sanity: alpha really is anti-multiplicative
    basis = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    ok = all(T.lin(alphaT, T.mul(u, v)) == T.mul(T.lin(alphaT, v), T.lin(alphaT, u))
             for u in basis for v in basis)
    print(f"   alpha(xy) = alpha(y)alpha(x) on the basis: {ok}")
    print()

    print("== cor:anti (4.5): the transpose on M_2(F_3) (anti-automorphism) ==")
    n = 4
    def mm(x, y):
        return [sum(x[i * 2 + t] * y[t * 2 + j] for t in range(2)) % p for i in range(2) for j in range(2)]
    def tr(x):
        return [x[j * 2 + i] for i in range(2) for j in range(2)]
    M2 = Alg(4, [[mm(u, v) for v in
                  [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]] for u in
                 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]], p)
    analyse("mu(x,y)=xy+y^T x^T", M2, lambda x, y: [(a + b) % p for a, b in zip(mm(x, y), mm(tr(y), tr(x)))])


if __name__ == "__main__":
    main()
