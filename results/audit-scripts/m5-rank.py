"""m5: small helper library: rank over F_p and the cor:criterion test.

determined(alg, mu) checks dim Zs_mu == dim ker bar-mu for a finite algebra
alg = (p, n, prods) with structure constants prods[(i,j)] (a tuple of length n),
exactly the assertion of cor:criterion.
"""
import itertools


def rank_over_Fp(rows, ncols, p):
    M = [list(r) for r in rows]
    rank = piv = 0
    while piv < ncols and rank < len(M):
        pr = None
        for i in range(rank, len(M)):
            if M[i][piv] % p:
                pr = i
                break
        if pr is None:
            piv += 1
            continue
        M[rank], M[pr] = M[pr], M[rank]
        inv = pow(M[rank][piv] % p, -1, p)
        M[rank] = [(v * inv) % p for v in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][piv] % p:
                f = M[i][piv] % p
                M[i] = [(M[i][k] - f * M[rank][k]) % p for k in range(ncols)]
        rank += 1
        piv += 1
    return rank


def determined(alg, mu, label="", verbose=True):
    p, n, _ = alg
    elts = [tuple(v) for v in itertools.product(range(p), repeat=n)]
    Mat = [[0] * (n * n) for _ in range(n)]
    for i in range(n):
        for j in range(n):
            v = mu(tuple(1 if k == i else 0 for k in range(n)),
                   tuple(1 if k == j else 0 for k in range(n)))
            for r in range(n):
                Mat[r][i * n + j] = v[r] % p
    rk = rank_over_Fp(Mat, n * n, p)
    tens = []
    for x in elts:
        for y in elts:
            if mu(x, y) == tuple([0] * n):
                tens.append([(x[i] * y[j]) % p for i in range(n) for j in range(n)])
    dz = rank_over_Fp(tens, n * n, p) if tens else 0
    ok = (dz == n * n - rk)
    if verbose:
        print(f"  [{label}] {len(tens)} zero pairs; rank bar-mu = {rk}; "
              f"dim ker = {n*n-rk}; dim Zs = {dz}; determined = {ok}")
    return ok, len(tens), rk, n * n - rk, dz
