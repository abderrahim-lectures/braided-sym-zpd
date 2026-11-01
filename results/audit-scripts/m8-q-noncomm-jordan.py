#!/usr/bin/env python3
"""Stress test of question q:noncomm of paper/braided-sym-zpd.tex.

q:noncomm (line 462-466) claims:
  "By Remark rem:inner the answer is affirmative, in characteristic other than 2,
   whenever alpha is inner, and every automorphism of a matrix algebra is inner;
   the question is therefore about algebras admitting an involutive automorphism
   that is not inner."

But rem:inner only proves: for inner alpha, A is determined by mu_alpha
(x,y) |-> xy + alpha(yx)  <=>  A is determined by the Jordan product x o y = xy+yx
(i.e. A is zJpd).  For alpha = id (inner, involutive) mu_alpha IS the Jordan product,
so the answer is affirmative for such A only if A is zJpd.

Here: A = M_2(F_p) x F_p[eps] (eps^2 = 0) is noncommutative, unital, char p != 2,
alpha = id is an inner involutive automorphism, and A is NOT zJpd -- so the answer
is negative, contradicting the claim.

The computation uses, for the Jordan product,
   Zs = span{ x (x) y : x o y = 0 } = span over y of { v (x) y : v in ker(x |-> x o y) }
(valid because {x : x o y = 0} is a linear subspace for each fixed y), and
   ker(bar-o) = kernel of the 6 x 36 matrix of the bilinear map.
Determined-by-mu  <=>  dim Zs = dim ker  (Bresar Prop 1.3 (i)<->(iii)).
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


def nullspace(A, p):
    """A: list of rows (m x n) over F_p. Returns a basis of {v : A v = 0}."""
    if not A:
        return []
    M = np.array(A, dtype=np.int64) % p
    m, n = M.shape
    pivcol = []
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i, c] % p), None)
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        M[r] = (M[r] * pow(int(M[r, c]) % p, p - 2, p)) % p
        for i in range(m):
            if i != r and M[i, c] % p:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        pivcol.append(c)
        r += 1
        if r == m:
            break
    free = [c for c in range(n) if c not in pivcol]
    basis = []
    for f in free:
        v = [0] * n
        v[f] = 1
        for i, c in enumerate(pivcol):
            v[c] = (-M[i, f]) % p
        basis.append(v)
    return basis


def jordan_analysis(name, mult, add, zero, neg, n, p, elems=None):
    """mult(x,y): product; add, neg; zero: zero vector; n: dim."""
    if elems is None:
        elems = [list(e) for e in itertools.product(range(p), repeat=n)]
    circ = lambda x, y: [(a + b) % p for a, b in zip(mult(x, y), mult(y, x))]
    # ker(bar-circ)
    cols = []
    for i in range(n):
        for j in range(n):
            ei = zero[:]
            ei[i] = 1
            ej = zero[:]
            ej[j] = 1
            cols.append(circ(ei, ej))
    rows = [[cols[c][k] for c in range(n * n)] for k in range(n)]
    dimker = n * n - rref_rank(rows, p)
    # Zs
    tens = []
    for y in elems:
        My = [[circ([1 if i == k else 0 for i in range(n)], y)[i] for k in range(n)] for i in range(n)]
        for v in nullspace(My, p):
            t = [0] * (n * n)
            for i in range(n):
                if v[i]:
                    for j in range(n):
                        t[i * n + j] = v[i] * y[j] % p
            tens.append(t)
    dimZs = rref_rank(tens, p)
    print(f"{name}: dim A = {n}, rank(bar-circ) = {n*n-dimker}, dim ker = {dimker}, "
          f"dim Zs = {dimZs}  ->  {'zJpd (determined by Jordan product)' if dimZs == dimker else 'NOT zJpd'}")
    return dimker, dimZs


# ------------------------------------------------------------ algebras
def dual_numbers(p):
    n = 2  # basis 1, eps ; (a,b)(c,d) = (ac, ad+bc)
    mult = lambda x, y: [x[0] * y[0] % p, (x[0] * y[1] + x[1] * y[0]) % p]
    return n, mult, [0, 0]


def mat2(p):
    n = 4
    def mult(x, y):
        return [sum(x[i * 2 + t] * y[t * 2 + j] for t in range(2)) % p for i in range(2) for j in range(2)]
    return n, mult, [0, 0, 0, 0]


def mat2_x_dual(p):
    n = 6  # (m_00, m_01, m_10, m_11, a, b)
    def mult(x, y):
        m = [sum(x[i * 2 + t] * y[t * 2 + j] for t in range(2)) % p for i in range(2) for j in range(2)]
        a0, b0, a1, b1 = x[4], x[5], y[4], y[5]
        return m + [a0 * a1 % p, (a0 * b1 + b0 * a1) % p]
    return n, mult, [0] * 6


def main():
    for p in (3, 5):
        print(f"--- field F_{p} ---")
        for name, alg in (("dual numbers K[eps]", dual_numbers),
                          ("M_2(F_p)", mat2),
                          ("M_2(F_p) x K[eps]", mat2_x_dual)):
            n, mult, zero = alg(p)
            jordan_analysis(name, mult, None, zero, None, n, p)


if __name__ == "__main__":
    main()
