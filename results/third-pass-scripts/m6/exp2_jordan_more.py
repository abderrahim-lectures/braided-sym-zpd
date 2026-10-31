"""Experiment 2: is every unital zpd algebra zJpd (determined by x*y + y*x)?
Tests more noncommutative unital zpd algebras: Tri(K,K^m,K) (upper triangular-ish),
Tri(M_2(K), K^2, K), M_2(K) (+K), T_3.
"""
import sys
sys.path.insert(0, '.')
from zpd import *


def alg_tri_K_a_b(p, a, b, m):
    """Tri(K^a, K^m, K^b): blocks (a x a), (a x m), (b x b); product
       (X, Y, Z)(X', Y', Z') = (XX', XY' + YZ', ZZ').  Basis:
       A-part e_i (i<a), M-part f_j (j<m), B-part g_k (k<b)."""
    N = a + m + b
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for i in range(a):
        for j in range(a):
            if i == j:
                T[i][j][j] = (T[i][j][j] + 1) % p
    for i in range(a):
        for j in range(m):
            T[i][a + j][a + j] = (T[i][a + j][a + j] + 1) % p
    for j in range(m):
        for k in range(b):
            T[a + j][a + m + k][a + j] = (T[a + j][a + m + k][a + j] + 1) % p
    for k in range(b):
        for l in range(b):
            if k == l:
                T[a + m + k][a + m + l][a + m + l] = (T[a + m + k][a + m + l][a + m + l] + 1) % p
    return T


def alg_M2_plus_K(p):
    """M_2(F_p) x F_p."""
    A = alg_matrix_units(2, p)
    n = len(A)
    N = n + 1
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                T[i][j][k] = A[i][j][k]
    T[n][n][n] = 1 % p
    return T


def report(name, n, T, p):
    d_m = determined(n, T, p)
    d_j = determined(n, jordan_mu_p(n, T, p), p)
    print(f"p={p}  {name:22s} n={n:2d}  dimZ_m/ker_m={d_m} zpd={d_m[0]==d_m[1]}   "
          f"dimZ_J/ker_J={d_j} zJpd={d_j[0]==d_j[1]}", flush=True)
    return d_m, d_j


if __name__ == '__main__':
    for p in (3, 5, 2):
        report("Tri(K,K,K)", 3, alg_tri_K_a_b(p, 1, 1, 1), p)
        report("Tri(K,K^2,K)", 4, alg_tri_K_a_b(p, 1, 2, 1), p)
        if p != 2:
            report("Tri(K,K^3,K)", 5, alg_tri_K_a_b(p, 1, 3, 1), p)
        report("M_2 + K", 5, alg_M2_plus_K(p), p)
        if p == 3:
            report("T_3", 6, alg_upper_triangular(3, p), p)
            report("Tri(M_2,K^2,K)", 7, None, p) if False else None
