"""Experiment 10 (general braidings):
(a) A = F_p^2 (zpd). Search all linear sigma on A(x)A with sigma^2 = id (involutions)
    for which (A, mu_sigma) is NOT determined; look for one working over F_2, F_3, F_5
    with the same integer matrix.
(b) commutative A = F_3^2: all linear alpha (81), which twisted products are determined?
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *


def algebra_K2(p):
    return alg_diagonal(2, p)


def mu_from_sigma(n, A, S, p):
    """mu(x,y) = m(x(x)y + sigma(x(x)y)); S is the (n*n)x(n*n) matrix of sigma."""
    T = A
    MU = [[[0] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            # sigma(e_i (x) e_j) = sum S[(i,j),(a,b)] e_a (x) e_b
            out = [0] * n
            for a in range(n):
                for b in range(n):
                    c = S[i * n + j][a * n + b] % p
                    if c:
                        prod = T[a][b]
                        for k in range(n):
                            if prod[k]:
                                out[k] = (out[k] + c * prod[k]) % p
            # plus m(e_i (x) e_j)
            for k in range(n):
                out[k] = (out[k] + T[i][j][k]) % p
            MU[i][j] = [x % p for x in out]
    return MU


def mat_mul_np(X, Y, N, p):
    return [[sum(X[i][k] * Y[k][j] for k in range(N)) % p for j in range(N)] for i in range(N)]


def scan_sigma(p, restrict_involution=True):
    n = 2
    A = algebra_K2(p)
    N = n * n
    bad = []
    tot = 0
    det = 0
    for code in range(p ** (N * N)):
        c = code
        S = [[0] * N for _ in range(N)]
        for i in range(N):
            for j in range(N):
                S[i][j] = c % p
                c //= p
        if restrict_involution:
            S2 = mat_mul_np(S, S, N, p)
            if any(S2[i][j] != (1 if i == j else 0) for i in range(N) for j in range(N)):
                continue
        tot += 1
        MU = mu_from_sigma(n, A, S, p)
        d = determined(n, MU, p)
        if d[0] == d[1]:
            det += 1
        else:
            bad.append((S, d))
    print(f"p={p} involutions={restrict_involution}: {tot} sigmas, {det} determined, {len(bad)} NOT determined")
    for S, d in bad[:4]:
        print("   sigma=", S, " dims", d)
    return bad


def alphas_twisted(p):
    """commutative A = F_p^2, mu_alpha(x,y) = xy + alpha(y)alpha(x); all linear alpha."""
    n = 2
    A = algebra_K2(p)
    out = []
    for code in range(p ** (n * n)):
        c = code
        al = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                al[i][j] = c % p
                c //= p
        MU = [[[0] * n for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(n):
                v = list(A[i][j])
                # alpha(e_j) = row j of al ; alpha(e_i) = row i
                aj = al[j]
                ai = al[i]
                prod = multiply(n, A, aj, ai, p)
                MU[i][j] = [(v[k] + prod[k]) % p for k in range(n)]
        d = determined(n, MU, p)
        multiplicative = all(
            multiply(n, A, al[i], al[j], p) ==
            [sum(al[k][l] * A[i][j][k] for k in range(n)) % p for l in range(n)]
            for i in range(n) for j in range(n))
        out.append((al, d[0] == d[1], multiplicative))
    print(f"p={p}: {len(out)} alpha; determined: {sum(1 for x in out if x[1])}; "
          f"multiplicative: {sum(1 for x in out if x[2])}")
    mism = [(al, det, mult) for al, det, mult in out if det != mult]
    print(f"   cases where determined != multiplicative: {len(mism)}")
    for al, det, mult in mism[:8]:
        print("   alpha=", al, "determined", det, "multiplicative", mult)
    return out


if __name__ == '__main__':
    if sys.argv[1] == 'sigma':
        scan_sigma(int(sys.argv[2]))
    else:
        alphas_twisted(int(sys.argv[2]))
