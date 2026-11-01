"""Experiment 16: twisted braiding mu_alpha(x,y) = xy + alpha(y)alpha(x) on the commutative zpd
algebra A = K^2, for a linear (non-multiplicative) alpha with integer entries.
Which alpha give a NON-determined product over at least two fields?  (sharpness of cor:twisted)
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *


def mu_twisted(n, A, alpha, p):
    MU = [[[0] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            v = list(A[i][j])
            prod = multiply(n, A, alpha[j], alpha[i], p)   # alpha(e_j)*alpha(e_i)
            MU[i][j] = [(v[k] + prod[k]) % p for k in range(n)]
    return MU


def is_mult(n, A, alpha, p):
    for i in range(n):
        for j in range(n):
            lhs = [sum(alpha[k][l] * A[i][j][k] for k in range(n)) % p for l in range(n)]
            rhs = multiply(n, A, alpha[i], alpha[j], p)
            if lhs != rhs:
                return False
    return True


def is_unital(n, A, alpha, p):
    # alpha(1) = 1
    one = [1] + [0] * (n - 1)
    img = [0] * n
    for i in range(n):
        if one[i]:
            for j in range(n):
                img[j] = (img[j] + alpha[i][j]) % p
    return img == one


if __name__ == '__main__':
    n = 2
    hits = []
    for code in range(1 << 4):
        alpha = [[0, 0], [0, 0]]
        for i in range(n):
            for j in range(n):
                alpha[i][j] = (code >> (i * n + j)) & 1
        res = {}
        for p in (2, 3, 5, 7):
            A = alg_diagonal(2, p)
            MU = mu_twisted(n, A, alpha, p)
            d = determined(n, MU, p)
            res[p] = (d, d[0] == d[1], is_mult(n, A, alpha, p), is_unital(n, A, alpha, p))
        fails = [p for p in res if not res[p][1]]
        if len(fails) >= 2:
            hits.append((alpha, res))
    print(f"0/1 alpha failing over >= 2 fields: {len(hits)}")
    for alpha, res in hits:
        print("  alpha =", alpha)
        for p in res:
            d, det, mult, uni = res[p]
            print(f"     p={p}: dims {d} determined={det} multiplicative={mult} unital={uni}")
