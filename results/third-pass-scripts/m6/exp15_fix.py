"""Experiment 15.
(C-fix) sigma : A(x)A -> A(x)A, A = K^2, with sigma^2 = id EXACTLY over Z (0/1 entries),
whose symmetrized product mu_sigma = m(1+sigma) is NOT determined, over at least two fields.
(B-fix) dual numbers: D(a + b eps) = a satisfies rem:derivations' hypothesis but is not a
braided-symmetric derivation.
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *
from exp10_sigma import mu_from_sigma


def sigma_sq_is_id(S):
    N = len(S)
    for i in range(N):
        for j in range(N):
            v = sum(S[i][k] * S[k][j] for k in range(N))
            if v != (1 if i == j else 0):
                return False
    return True


def scan():
    N = 4
    hits = []
    for code in range(1 << (N * N)):
        S = [[0] * N for _ in range(N)]
        c = code
        for i in range(N):
            for j in range(N):
                S[i][j] = (c >> (i * N + j)) & 1
        if not sigma_sq_is_id(S):
            continue
        res = {}
        for p in (2, 3, 5, 7):
            A = alg_diagonal(2, p)
            MU = mu_from_sigma(2, A, S, p)
            d = determined(2, MU, p)
            res[p] = (d, d[0] == d[1])
        fails = [p for p in res if not res[p][1]]
        if len(fails) >= 2:
            hits.append((S, res))
    print(f"involutions sigma^2 = id over Z: found {len(hits)} that fail determination over >= 2 fields")
    hits.sort(key=lambda h: -len([p for p in h[1] if not h[1][p][1]]))
    for S, res in hits[:6]:
        print("  sigma =", S)
        print("     ", {p: res[p] for p in res})
    return hits


def dual_witness_fixed(p=5):
    n = 2
    A = alg_dual_numbers(p)
    alpha = [[1, 0], [0, p - 1]]
    def mu(x, y):
        xy = multiply(n, A, x, y, p)
        yx = multiply(n, A, y, x, p)
        ayx = [sum(yx[i] * alpha[i][j] for i in range(n)) % p for j in range(n)]
        return [(u + v) % p for u, v in zip(xy, ayx)]
    elems = list(product(range(p), repeat=n))
    D = lambda v: (v[0], 0)          # a + b eps |-> a
    zero = [(x, y) for x in elems for y in elems if not any(mu(x, y))]
    good = all(not any([(u + v) % p for u, v in zip(mu(D(x), y), mu(x, D(y)))]) for x, y in zero)
    isder = all(sorted(D(mu(x, y))) == sorted([(u + v) % p for u, v in zip(mu(D(x), y), mu(x, D(y)))])
                for x in elems for y in elems)
    wit = None
    for x in elems:
        for y in elems:
            lhs = D(mu(x, y))
            rhs = [(u + v) % p for u, v in zip(mu(D(x), y), mu(x, D(y)))]
            if list(lhs) != list(rhs):
                wit = (x, y, list(lhs), rhs)
                break
        if wit:
            break
    print(f"(B) dual numbers over F_{p}: D(a + b eps) = a.")
    print(f"    hypothesis of rem:derivations on all {len(zero)} mu-zero pairs: {good}")
    print(f"    D a braided-symmetric derivation: {isder};  witness of failure: {wit}")


if __name__ == '__main__':
    dual_witness_fixed(5)
    dual_witness_fixed(3)
    print()
    scan()
