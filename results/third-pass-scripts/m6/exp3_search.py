"""Experiment 3: exhaustive / random search for a unital zpd algebra that is NOT zJpd.

Family: A = K.1 + V with V^2 subset V (so A is unital associative for every bilinear
beta : V x V -> V).  dim V = 2 over F_3 is exhaustive (6561 algebras); dim V = 3 over
F_2 sampled and over F_3 sampled; also dim V = 3 over F_2 exhaustively if asked.
"""
import sys, itertools, random
sys.path.insert(0, '.')
from zpd import *


def alg_from_beta(p, d, beta):
    """d = dim V; returns table of A = K.1 + V (basis: e0 = 1, e1..ed = V)."""
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


def all_betas(p, d):
    N = d * d * d
    for code in range(p ** N):
        c = code
        beta = [[[0] * d for _ in range(d)] for _ in range(d)]
        for idx in range(N):
            i = idx // (d * d)
            j = (idx // d) % d
            k = idx % d
            beta[i][j][k] = c % p
            c //= p
        yield beta


def zpd_zjpd(n, T, p):
    dm = determined(n, T, p)
    if dm[0] != dm[1]:
        return None
    dj = determined(n, jordan_mu_p(n, T, p), p)
    return (dm, dj)


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'exh'
    if mode == 'exh':
        p, d = 3, 2
        bad = []
        cnt = 0
        zpd_cnt = 0
        for beta in all_betas(p, d):
            T = alg_from_beta(p, d, beta)
            if not is_associative(d + 1, T, p):
                continue
            r = zpd_zjpd(d + 1, T, p)
            cnt += 1
            if r is not None:
                zpd_cnt += 1
                if r[1][0] != r[1][1]:
                    bad.append((beta, r))
        print(f"p={p} dim V={d}: {cnt} algebras, {zpd_cnt} zpd, {len(bad)} zpd but not zJpd")
        for beta, r in bad[:5]:
            print(beta, r)
    else:
        p = int(sys.argv[2]); d = int(sys.argv[3]); count = int(sys.argv[4])
        random.seed(12345)
        zpd_cnt = 0
        bad = []
        for _ in range(count):
            beta = [[[random.randrange(p) for _ in range(d)] for _ in range(d)] for _ in range(d)]
            T = alg_from_beta(p, d, beta)
            r = zpd_zjpd(d + 1, T, p)
            if r is not None:
                zpd_cnt += 1
                if r[1][0] != r[1][1]:
                    bad.append((beta, r))
        print(f"p={p} dim V={d}: {count} random algebras, {zpd_cnt} zpd, {len(bad)} zpd but not zJpd")
        for beta, r in bad[:3]:
            print(beta, r)
