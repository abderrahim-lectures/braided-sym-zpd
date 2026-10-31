"""Experiment 5: structured candidates for 'unital zpd but not zJpd', tested over several
fields at once (an integer structure-constant family, reduced mod p).
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *


def alg_unit_plus(p, B):
    """A = K.1 + V, V given by its multiplication table B (dim d), V^2 subset V."""
    d = len(B)
    n = d + 1
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    for j in range(n):
        T[0][j][j] = 1 % p
        T[j][0][j] = 1 % p
    for i in range(d):
        for j in range(d):
            for k in range(d):
                T[i + 1][j + 1][k + 1] = B[i][j][k] % p
    return T


def table_from_units(n, pairs, p):
    """upper triangular style: pairs = [(i,j)] with E_ij E_kl = delta_jk E_il within the set."""
    pos = {pr: k for k, pr in enumerate(pairs)}
    N = len(pairs)
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for a, (i, j) in enumerate(pairs):
        for b, (k, l) in enumerate(pairs):
            if j == k and (i, l) in pos:
                T[a][b][pos[(i, l)]] = (T[a][b][pos[(i, l)]] + 1) % p
    return T


def strict_upper(n, p):
    """strictly upper triangular n x n: E_ij, i<j."""
    return table_from_units(n, [(i, j) for i in range(n) for j in range(i + 1, n)], p)


def direct_sum(T1, T2, p):
    n1, n2 = len(T1), len(T2)
    N = n1 + n2
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for i in range(n1):
        for j in range(n1):
            for k in range(n1):
                T[i][j][k] = T1[i][j][k]
    for i in range(n2):
        for j in range(n2):
            for k in range(n2):
                T[n1 + i][n1 + j][n1 + k] = T2[i][j][k]
    return T


def tensor_with_dual(T1, p):
    """T1 (x) K[eps]/(eps^2): basis (a,0),(0,a).  dim 2*dim T1."""
    n1 = len(T1)
    N = 2 * n1
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for i in range(n1):
        for j in range(n1):
            for k in range(n1):
                c = T1[i][j][k] % p
                if c:
                    # (e_i,0)(e_j,0) = (e_iej,0)
                    T[i][j][k] = (T[i][j][k] + c) % p
                    # (e_i,0)(0,e_j) = (0, e_ie_j)
                    T[i][n1 + j][n1 + k] = (T[i][n1 + j][n1 + k] + c) % p
                    # (0,e_i)(e_j,0) = (0, e_ie_j)
                    T[n1 + i][j][n1 + k] = (T[n1 + i][j][n1 + k] + c) % p
    return T


def test(name, T, p):
    n = len(T)
    assert is_associative(n, T, p), f"{name}: not associative over F_{p}"
    dm = determined(n, T, p)
    dj = determined(n, jordan_mu_p(n, T, p), p)
    zpd = dm[0] == dm[1]
    zj = dj[0] == dj[1]
    flag = "  <== zpd but NOT zJpd" if (zpd and not zj) else ""
    print(f"p={p} {name:26s} n={n}  product {dm} zpd={zpd}  Jordan {dj} zJpd={zj}{flag}", flush=True)
    return zpd, zj


if __name__ == '__main__':
    for p in (2, 3, 5, 7):
        T2 = alg_diagonal(2, p)          # K^2
        test("T_2 + K", direct_sum(alg_upper_triangular(2, p), alg_diagonal(1, p), p), p)
        test("K + T_2 (unit plus)", alg_unit_plus(p, alg_upper_triangular(2, p)), p)
        test("K + strict-upper 3x3", alg_unit_plus(p, strict_upper(3, p)), p)
        test("T_2 (x) dual numbers", tensor_with_dual(alg_upper_triangular(2, p), p), p)
        test("M_2 (x) dual numbers", tensor_with_dual(alg_matrix_units(2, p), p), p) if p != 2 else None
    print()
    # one specific integer family over many primes: A = K + V, V = the 3-dim algebra
    # with basis a,b,c and products a^2 = b, ab = c, ba = 0, ... (tested individually below)
