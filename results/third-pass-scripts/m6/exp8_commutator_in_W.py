"""Experiment 8: is [A,A] contained in W = span{xy : x o y = 0} ?
If yes for a unital algebra (char != 2), then  zpd  ==>  zJpd :  any phi vanishing on
zero Jordan products is lambda(xy) by zpd, and lambda(xy)-lambda(yx) = lambda([x,y]) = 0
once [x,y] is a sum of products of Jordan-orthogonal pairs.
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *
from exp5_structured import alg_unit_plus, table_from_units, direct_sum, tensor_with_dual
from exp7_families import ladder, quantum_plane, subalg_T3


def W_and_commutators(n, T, p):
    elems = list(product(range(p), repeat=n))
    W = []
    for x in elems:
        for y in elems:
            xy = multiply(n, T, x, y, p)
            yx = multiply(n, T, y, x, p)
            if not any((a + b) % p for a, b in zip(xy, yx)):
                W.append(xy)
    C = []
    basis = [[1 if k == i else 0 for k in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            xy = multiply(n, T, basis[i], basis[j], p)
            yx = multiply(n, T, basis[j], basis[i], p)
            C.append([(a - b) % p for a, b in zip(xy, yx)])
    dimW = rank(W, p, n) if W else 0
    dimC = rank(C, p, n)
    return dimW, dimC, W, C


def contains(W, C, p, n):
    if not W:
        return all(not any(c) for c in C)
    # rank of W equals rank of W+C ?
    rW = rank(W, p, n)
    rWC = rank(W + C, p, n)
    return rW == rWC


def report(name, T, p):
    n = len(T)
    dimW, dimC, W, C = W_and_commutators(n, T, p)
    ok = contains(W, C, p, n)
    print(f"p={p} {name:26s} n={n} dimW={dimW} dim[A,A]={dimC} [A,A]<=W: {ok}", flush=True)
    return ok


if __name__ == '__main__':
    for p in (3, 5):
        report("T_2", alg_upper_triangular(2, p), p)
        report("M_2", alg_matrix_units(2, p), p)
        report("T_2 + K", direct_sum(alg_upper_triangular(2, p), alg_diagonal(1, p), p), p)
        report("ladder (not zpd)", ladder(p), p)
        report("quantum plane q=2", quantum_plane(p, 2), p)
        report("K + strict upper 3", alg_unit_plus(p, __import__('exp5_structured').strict_upper(3, p)), p)
        report("subalg T_3", subalg_T3(p), p)
        report("T_3", alg_upper_triangular(3, p), p)
