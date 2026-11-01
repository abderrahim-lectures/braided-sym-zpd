#!/usr/bin/env python3
"""Finite-dimensional algebra checks for the audit of paper/braided-sym-zpd.tex.

Conventions.  An algebra A over F_p is given by a bilinear map mu(x,y) -> list of n
ints; elements are tuples in F_p^n, and A (x) A is identified with F_p^{n^2} by
(i,j) <-> e_i (x) e_j, index i*n+j.

For a bilinear mu we compute
  * rank r of mu-bar : A(x)A -> A  (so dim ker = n^2 - r),
  * the number of pairs (x,y) with mu(x,y) = 0,
  * dim Zs_mu = dim span{ x (x) y : mu(x,y) = 0 }.
By Bresar Prop 1.3 (i)<->(iii), as recalled in the paper: A is determined by mu
iff dim Zs_mu = dim ker mu-bar.
"""
import itertools
import numpy as np


# ------------------------------------------------------------------ linear algebra
def rref_rank(rows, p):
    rows = [np.array(r, dtype=np.int64) % p for r in rows]
    if not rows:
        return 0
    M = np.array(rows) % p
    nr, nc = M.shape
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if M[i, c] % p:
                piv = i
                break
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


def mu_bar_rows(mu, n, p):
    cols = []
    for i in range(n):
        for j in range(n):
            ei = [0] * n
            ei[i] = 1
            ej = [0] * n
            ej[j] = 1
            cols.append([c % p for c in mu(ei, ej)])
    return [[cols[c][k] for c in range(n * n)] for k in range(n)]


def analyse(name, mu, n, p, verbose=True):
    rank = rref_rank(mu_bar_rows(mu, n, p), p)
    dimker = n * n - rank
    zero_tensors = []
    cnt = 0
    for x in itertools.product(range(p), repeat=n):
        xl = list(x)
        for y in itertools.product(range(p), repeat=n):
            if not any(c % p for c in mu(xl, list(y))):
                cnt += 1
                v = [0] * (n * n)
                for i in range(n):
                    if x[i]:
                        for j in range(n):
                            v[i * n + j] = x[i] * y[j] % p
                zero_tensors.append(v)
    dimZs = rref_rank(zero_tensors, p)
    if verbose:
        print(f"{name}: dim A = {n}, rank(mu-bar) = {rank}, dim ker(mu-bar) = {dimker}, "
              f"#zero pairs = {cnt} of {p ** (2 * n)}, dim Zs = {dimZs}, "
              f"{'DETERMINED' if dimZs == dimker else 'NOT determined'}")
    return dict(name=name, n=n, p=p, rank=rank, dimker=dimker, nzero=cnt, dimZs=dimZs)


# ------------------------------------------------------------------ matrix helpers
def matmul(x, y, n, m=None):
    m = n if m is None else m
    k = len(x) // n
    return [sum(x[i * k + t] * y[t * m + j] for t in range(k)) for i in range(n) for j in range(m)]


def matT(x, n):
    return [x[j * n + i] for i in range(n) for j in range(n)]


def add(*vs):
    return [sum(c) for c in zip(*vs)]


def main():
    p = 3
    n = 2
    N = 4
    D = [1, 0, 0, -1]
    conj = lambda m: matmul(matmul(D, m, n), D, n)  # D = D^{-1}

    print("=== Paper, Sec. 4: M_2(F_3) ===")
    analyse('prop:matrix  mu(x,y)=xy+alpha(yx), alpha=conj diag(1,-1)',
            lambda x, y: add(matmul(x, y, n), conj(matmul(y, x, n))), N, p)
    analyse('ordinary xy', lambda x, y: matmul(x, y, n), N, p)
    analyse('transpose twist  xy + y^T x^T',
            lambda x, y: add(matmul(x, y, n), matmul(matT(y, n), matT(x, n), n)), N, p)
    analyse('2xy (identity braiding)',
            lambda x, y: add(matmul(x, y, n), matmul(x, y, n)), N, p)
    analyse('Jordan  xy+yx',
            lambda x, y: add(matmul(x, y, n), matmul(y, x, n)), N, p)


if __name__ == "__main__":
    main()


def dual_numbers_checks():
    """Example ex:dual: A = K[eps]/(eps^2), char != 2, mu(x,y) = f(xy), f = id + alpha,
    alpha(a+b eps) = a - b eps, so f(a + b eps) = 2a. Also the ordinary product."""
    for p in (3, 5):
        n = 2  # basis 1, eps

        def mul(x, y):
            return [x[0] * y[0] % p, (x[0] * y[1] + x[1] * y[0]) % p]

        f = lambda z: [2 * z[0] % p, 0]
        mu = lambda x, y: f(mul(x, y))
        print(f"--- ex:dual over F_{p} (char != 2) ---")
        analyse("mu_alpha(x,y) = f(xy), f = id + alpha", mu, n, p)
        analyse("ordinary product xy (for the 'not zpd' claim)", mul, n, p)


if __name__ == "__main__":
    dual_numbers_checks()
