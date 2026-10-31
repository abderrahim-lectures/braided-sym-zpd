"""Experiment 11: M_2(B) for various unital B (always zpd by Bresar Cor 2.17(a)).
   - is it zJpd?   (Bresar-Grasic-Sanchez-Ortega: only under technical restrictions)
   - is the twisted product xy + alpha(yx) determined, for involutive automorphisms alpha?
"""
import sys
sys.path.insert(0, '.')
from zpd import *


def mat_alg(n, B, p):
    """M_n(B) for B an algebra given by its table (dim d): basis (i,j,a) -> i*d*n + j*d + a."""
    d = len(B)
    N = n * n * d
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    def idx(i, j, a):
        return (i * n + j) * d + a
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    if j == k:
                        for a in range(d):
                            for b in range(d):
                                for c in range(d):
                                    if B[a][b][c]:
                                        T[idx(i, j, a)][idx(k, l, b)][idx(i, l, c)] = \
                                            (T[idx(i, j, a)][idx(k, l, b)][idx(i, l, c)] + B[a][b][c]) % p
    return T


def dual(p):
    return alg_dual_numbers(p)


def KxK(p):
    return alg_diagonal(2, p)


def Kx3(p):
    """K[x]/(x^3)."""
    n = 3
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    T[0][0] = [1, 0, 0]
    T[0][1] = [0, 1, 0]
    T[1][0] = [0, 1, 0]
    T[0][2] = [0, 0, 1]
    T[2][0] = [0, 0, 1]
    T[1][1] = [0, 0, 1]
    return [[[x % p for x in T[i][j]] for j in range(n)] for i in range(n)]


def conj_mu(n, B, p, alpha_el):
    """mu(x,y) = x*y + alpha(y*x) where alpha = conjugation by an invertible element."""
    d = len(B)
    N = n * n * d
    # element as n x n matrix over B: entry (i,j) = list of d coeffs
    def to_mat(v):
        return [[v[(i * n + j) * d:(i * n + j + 1) * d] for j in range(n)] for i in range(n)]
    def from_mat(M):
        out = []
        for i in range(n):
            for j in range(n):
                out.extend([x % p for x in M[i][j]])
        return out
    def bmul(u, v):
        return multiply(d, B, u, v, p)
    A = to_mat(alpha_el)
    # invert A over M_n(B): use the standard adjugate-free approach (n=2!)
    assert n == 2
    a, b = A[0][0], A[0][1]
    c, dd = A[1][0], A[1][1]
    one = [1] + [0] * (d - 1)
    det = [(x - y) % p for x, y in zip(bmul(a, dd), bmul(b, c))]
    deti = invert_in_B(d, B, det, p)
    Ainv = [[bmul(dd, deti), [(-x) % p for x in bmul(b, deti)]],
            [[(-x) % p for x in bmul(c, deti)], bmul(a, deti)]]
    def alpha(v):
        M = to_mat(v)
        # A M A^{-1}
        AM = [[None] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                acc = [0] * d
                for k in range(n):
                    pr = bmul(A[i][k], M[k][j])
                    acc = [(x + y) % p for x, y in zip(acc, pr)]
                AM[i][j] = acc
        out = [[None] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                acc = [0] * d
                for k in range(n):
                    pr = bmul(AM[i][k], Ainv[k][j])
                    acc = [(x + y) % p for x, y in zip(acc, pr)]
                out[i][j] = acc
        return from_mat(out)
    # build mu table
    MU = [[[0] * N for _ in range(N)] for _ in range(N)]
    # index helper for the N-dim algebra M_n(B)
    def idx(i, j, a):
        return (i * n + j) * d + a
    basis = [[1 if k == i else 0 for k in range(N)] for i in range(N)]
    for I in range(N):
        for J in range(N):
            xy = multiply(N, T, basis[I], basis[J], p)
            yx = multiply(N, T, basis[J], basis[I], p)
            ayx = alpha(yx)
            MU[I][J] = [(u + v) % p for u, v in zip(xy, ayx)]
    return MU


def invert_in_B(d, B, x, p):
    """inverse of x in the algebra B (assumed unital, commutative enough); brute force."""
    from itertools import product as prod
    for cand in prod(range(p), repeat=d):
        pr = multiply(d, B, list(cand), x, p)
        if pr[0] % p == 1 % p and all(c == 0 for c in pr[1:]):
            return list(cand)
    raise ValueError("not invertible")


def report(name, T, MU_list, p):
    n = len(T)
    dm = determined(n, T, p)
    print(f"p={p} {name}: dim={n} product {dm} zpd={dm[0]==dm[1]}", flush=True)
    dj = determined(n, jordan_mu_p(n, T, p), p)
    print(f"        Jordan {dj} zJpd={dj[0]==dj[1]}", flush=True)
    for lab, MU in MU_list:
        d = determined(n, MU, p)
        print(f"        twisted ({lab}) {d} determined={d[0]==d[1]}", flush=True)


if __name__ == '__main__':
    p = int(sys.argv[1])
    for Bname, B in (("dual", dual(p)), ("KxK", KxK(p)), ("K[x]/x^3", Kx3(p))):
        n = 2
        d = len(B)
        N = n * n * d
        if N > 8:
            continue
        T = mat_alg(n, B, p)
        assert is_associative(N, T, p), f"M_2({Bname}) not associative"
        # alpha1 = conj by diag(1,-1) : entries in B
        one = [1] + [0] * (d - 1)
        zero = [0] * d
        negone = [(-x) % p for x in one]
        D = [[one, zero], [zero, negone]]
        def flatten(M):
            out = []
            for i in range(n):
                for j in range(n):
                    out.extend([x % p for x in M[i][j]])
            return out
        a1 = flatten(D)
        S = [[zero, one], [one, zero]]
        a2 = flatten(S)
        MU1 = conj_mu(n, B, p, a1)
        MU2 = conj_mu(n, B, p, a2)
        report(f"M_2({Bname})", T, [("conj diag(1,-1)", MU1), ("conj swap", MU2)], p)
