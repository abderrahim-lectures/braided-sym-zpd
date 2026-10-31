"""Experiment 12: q:noncomm.  Noncommutative zpd algebras with an INVOLUTIVE AUTOMORPHISM
alpha; is xy + alpha(y)alpha(x) (= xy + alpha(yx) when alpha is multiplicative) determined?
"""
import sys
sys.path.insert(0, '.')
from zpd import *
from exp5_structured import direct_sum


def mu_twisted(n, T, alpha_mat, p):
    """mu(x,y) = x*y + alpha(y)*alpha(x); alpha given by its matrix (alpha(e_i) = row i)."""
    MU = [[[0] * n for _ in range(n)] for _ in range(n)]
    a = [[alpha_mat[i][j] % p for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            v = list(T[i][j])
            # alpha(e_j) = a[j], alpha(e_i) = a[i]
            prod = multiply(n, T, a[j], a[i], p)
            MU[i][j] = [(v[k] + prod[k]) % p for k in range(n)]
    return MU


def involution_check(n, a, p):
    a2 = [[sum(a[i][k] * a[k][j] for k in range(n)) % p for j in range(n)] for i in range(n)]
    return all(a2[i][j] == (1 if i == j else 0) % p for i in range(n) for j in range(n))


def mul_alpha(n, a, p, x, y):
    """alpha(x*y) vs alpha(x)*alpha(y) check for multiplicativity."""
    pass


def is_automorphism(n, T, a, p):
    basis = [[1 if k == i else 0 for k in range(n)] for i in range(n)]
    def ap(v):
        out = [0] * n
        for i in range(n):
            if v[i]:
                for j in range(n):
                    if a[i][j]:
                        out[j] = (out[j] + v[i] * a[i][j]) % p
        return out
    for i in range(n):
        for j in range(n):
            if ap(multiply(n, T, basis[i], basis[j], p)) != multiply(n, T, ap(basis[i]), ap(basis[j]), p):
                return False
    return True


def report(name, T, p, alphas):
    n = len(T)
    dm = determined(n, T, p)
    dj = determined(n, jordan_mu_p(n, T, p), p)
    print(f"p={p} {name}: dim={n} zpd={dm[0]==dm[1]} {dm}  zJpd={dj[0]==dj[1]} {dj}", flush=True)
    for lab, a in alphas:
        assert involution_check(n, a, p), f"{lab} not an involution"
        assert is_automorphism(n, T, a, p), f"{lab} not an automorphism"
        MU = mu_twisted(n, T, a, p)
        d = determined(n, MU, p)
        print(f"        alpha={lab}: dimZ={d[0]} dimker={d[1]} determined={d[0]==d[1]}", flush=True)


if __name__ == '__main__':
    p = int(sys.argv[1])
    M2 = alg_matrix_units(2, p)
    T2 = alg_upper_triangular(2, p)
    # A = M_2 x M_2 with the swap automorphism
    A = direct_sum(M2, M2, p)
    nA = len(A)
    swap = [[0] * nA for _ in range(nA)]
    for i in range(4):
        swap[i][4 + i] = 1
        swap[4 + i][i] = 1
    report("M_2 x M_2", A, p, [("swap", swap)])
    # A = T_2 x T_2 with swap
    B = direct_sum(T2, T2, p)
    nB = len(B)
    swapB = [[0] * nB for _ in range(nB)]
    for i in range(3):
        swapB[i][3 + i] = 1
        swapB[3 + i][i] = 1
    report("T_2 x T_2", B, p, [("swap", swapB)])
    # A = M_2 x K with conjugation by diag(1,-1) on the first factor
    C = direct_sum(M2, alg_diagonal(1, p), p)
    nC = len(C)
    Dm = [[0] * nC for _ in range(nC)]
    # M_2 basis index: i*2+j ; conj by diag(1,-1) negates E12 and E21, fixes E11, E22
    for i in range(nC):
        Dm[i][i] = 1
    Dm[1][1] = p - 1   # E12 -> -E12
    Dm[2][2] = p - 1   # E21 -> -E21
    report("M_2 x K", C, p, [("conj diag(1,-1)", Dm)])
