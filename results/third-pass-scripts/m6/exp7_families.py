"""Experiment 7: explicit candidate families (associative by construction, unital), tested
over several fields, looking for 'zpd but not zJpd'.
"""
import sys
sys.path.insert(0, '.')
from zpd import *
from exp5_structured import alg_unit_plus, table_from_units, direct_sum, test


def ladder(p):
    """A = K.1 + V, V=span{a,b,c} with a*b=c, all other products 0 (V^2 concentrated)."""
    B = [[[0, 0, 0] for _ in range(3)] for _ in range(3)]
    B[0][1][2] = 1
    return alg_unit_plus(p, B)


def quantum_plane(p, q):
    """K<x,y>/(x^2, y^2, yx - q xy): basis 1,x,y,xy."""
    n = 4
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    T[0] = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
    for j in range(n):
        T[j][0] = [1 if k == j else 0 for k in range(n)]
    T[1][2] = [0, 0, 0, 1]          # x y = xy
    T[2][1] = [0, 0, 0, q % p]      # y x = q xy
    return [[[x % p for x in T[i][j]] for j in range(n)] for i in range(n)]


def trivial_extension_T2(p):
    """A = T_2 + K with M=K the 1-dim module (e11 acts as 1, e22 as 0, e12 as 0), M^2 = 0."""
    n = 4
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    # T_2 part on e0,e1,e2
    T[0][0][0] = 1; T[0][1][1] = 1; T[1][2][1] = 1; T[0][2][2] = 1; T[2][2][2] = 1
    # e0 acts as 1 on m=e3, others 0
    T[0][3][3] = 1; T[3][0][3] = 1
    return [[[x % p for x in T[i][j]] for j in range(n)] for i in range(n)]


def subalg_T3(p):
    """span{E11, E12, E13, E33} inside T_3 (unit E11+E33)."""
    return table_from_units(3, [(0, 0), (0, 1), (0, 2), (2, 2)], p)


def trivial_extension_Kx2(p):
    """A = K[x]/x^2 + K[x]/x^2 with M^2 = 0 (regular module): dim 4, commutative."""
    n = 4
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    T[0][0][0] = 1; T[0][1][1] = 1; T[1][0][1] = 1
    T[0][2][2] = 1; T[0][3][3] = 1; T[1][2][3] = 1; T[2][1][3] = 1
    return [[[x % p for x in T[i][j]] for j in range(n)] for i in range(n)]


if __name__ == '__main__':
    for p in (2, 3, 5):
        test("ladder K+V(ab=c)", ladder(p), p)
        test("quantum plane q=0", quantum_plane(p, 0), p)
        if p > 2:
            test("quantum plane q=2", quantum_plane(p, 2), p)
        test("trivial ext T_2+K", trivial_extension_T2(p), p)
        test("subalg T_3 (4-dim)", subalg_T3(p), p)
        test("trivial ext K[x]/x^2", trivial_extension_Kx2(p), p)
        print(flush=True)
