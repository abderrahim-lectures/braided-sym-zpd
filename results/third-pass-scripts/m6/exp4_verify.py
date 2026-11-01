"""Experiment 4: independent verification of a dim-4 unital zpd algebra over F_3 that is
NOT zJpd (not determined by x*y + y*x).

verification is brute force: all p^n x p^n pairs, no kernel-basis shortcut.
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *

BETA = [[[2, 1, 0], [2, 1, 1], [0, 1, 2]],
        [[2, 0, 2], [2, 1, 0], [0, 1, 2]],
        [[2, 0, 1], [2, 1, 1], [2, 1, 0]]]


def alg(p, beta=BETA):
    d = len(beta)
    n = d + 1
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    for j in range(n):
        T[0][j][j] = 1 % p
        T[j][0][j] = 1 % p
    for i in range(d):
        for j in range(d):
            for k in range(d):
                T[i + 1][j + 1][k + 1] = beta[i][j][k] % p
    return T


def brute(n, T, p, mu):
    """dim span{x(x)y : mu(x,y)=0}, dim ker mu-bar, and the set of zero pairs."""
    elems = list(product(range(p), repeat=n))
    gens = []
    for x in elems:
        for y in elems:
            if not any(mu(n, T, x, y, p)):
                t = [0] * (n * n)
                for i in range(n):
                    if x[i]:
                        for j in range(n):
                            if y[j]:
                                t[i * n + j] = (x[i] * y[j]) % p
                gens.append(t)
    U = [[0] * (n * n) for _ in range(n)]
    for x in product(range(p), repeat=n):
        pass
    # matrix of mu-bar
    for i in range(n):
        for j in range(n):
            e = [0] * n
            e[i] = 1
            f = [0] * n
            f[j] = 1
            v = mu(n, T, e, f, p)
            for k in range(n):
                U[k][i * n + j] = v[k]
    dimker = len(kernel(U, p, n * n))
    dimZ = rank(gens, p, n * n) if gens else 0
    return dimZ, dimker


def mul_m(n, T, x, y, p):
    return multiply(n, T, x, y, p)


def mul_J(n, T, x, y, p):
    xy = multiply(n, T, x, y, p)
    yx = multiply(n, T, y, x, p)
    return [(a + b) % p for a, b in zip(xy, yx)]


def run(p):
    n = 4
    T = alg(p)
    assert is_associative(n, T, p), "not associative"
    assert has_unit(n, T, p), "no unit"
    zm = brute(n, T, p, mul_m)
    zj = brute(n, T, p, mul_J)
    print(f"p={p}: product: dimZ={zm[0]} dimker={zm[1]} -> zpd={zm[0]==zm[1]};   "
          f"Jordan: dimZ={zj[0]} dimker={zj[1]} -> zJpd={zj[0]==zj[1]}")
    # commutativity?
    basis = [[1 if k == i else 0 for k in range(n)] for i in range(n)]
    comm = all(multiply(n, T, basis[i], basis[j], p) == multiply(n, T, basis[j], basis[i], p)
               for i in range(n) for j in range(n))
    print("   commutative:", comm)
    return T, zm, zj


def witness(p):
    """explicit phi in Z_J^perp that is not in ker(bar J)^perp: a bilinear functional
    vanishing on every zero Jordan product but not factorable through the Jordan product."""
    n = 4
    T = alg(p)
    elems = list(product(range(p), repeat=n))
    # constraints: phi . (x (x) y) = 0 for every zero Jordan pair
    rows = []
    for x in elems:
        for y in elems:
            if not any(mul_J(n, T, x, y, p)):
                t = [0] * (n * n)
                for i in range(n):
                    if x[i]:
                        for j in range(n):
                            if y[j]:
                                t[i * n + j] = (x[i] * y[j]) % p
                rows.append(t)
    # annihilator of the span of rows: solve rows . phi = 0 for phi in F_p^{n*n}
    M = [[rows[r][c] for r in range(len(rows))] for c in range(n * n)]
    annZ = kernel(M, p, n * n - 0) if False else kernel(
        [[rows[r][c] for c in range(n * n)] for r in range(len(rows))], p, n * n)
    # annZ = {phi : phi vanishes on every zero Jordan tensor}  (as vectors of length n*n)
    # kernel of bar J
    U = [[0] * (n * n) for _ in range(n)]
    for i in range(n):
        for j in range(n):
            e = [0] * n
            e[i] = 1
            f = [0] * n
            f[j] = 1
            v = mul_J(n, T, e, f, p)
            for k in range(n):
                U[k][i * n + j] = v[k]
    kerJ = kernel(U, p, n * n)
    for phi in annZ:
        for u in kerJ:
            val = sum(phi[c] * u[c] for c in range(n * n)) % p
            if val:
                # find a concrete pair of tensors: u = sum over basis tensors
                pairs = []
                for c in range(n * n):
                    if u[c]:
                        pairs.append((c // n, c % n, u[c]))
                print(f"p={p}: phi = {phi}")
                print(f"   phi vanishes on all {len(rows)} zero-Jordan tensors, but phi(u) = {val}")
                print(f"   u = sum c_i e_i(x)e_j with (i,j,c): {pairs}")
                return phi, u
    return None


if __name__ == '__main__':
    for p in (3, 5, 7):
        run(p)
    witness(3)
