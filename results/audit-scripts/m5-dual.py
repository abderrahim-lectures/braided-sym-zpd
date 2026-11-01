"""m5: ex:dual checked by brute force.

A = F_p[eps]/(eps^2) = {(a,b)}, (a,b)(c,d) = (ac, ad+bc).
  * ordinary product: A is not zpd (ex:dual, via Bresar Theorem 2.27);
  * twisted product mu_alpha(x,y) = xy + alpha(y)alpha(x), alpha(a+b eps) = a - b eps,
    i.e. f(xy) with f = id + alpha, f(a,b) = (2a, 0): A is determined (thm:codim);
  * the only idempotents are 0 and 1 when char != 2, and 1 + eps is also idempotent
    when char = 2 (so the hypothesis char != 2 is used twice).
"""
# ---- inlined from results/audit-scripts/m5-rank.py
# (kept verbatim so this script is self-contained)
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


for p in (3, 5, 7):
    prods = {}
    for i in range(2):
        for j in range(2):
            out = [0, 0]
            if (i, j) == (0, 0):
                out[0] = 1
            if (i, j) == (0, 1) or (i, j) == (1, 0):
                out[1] = 1
            prods[(i, j)] = tuple(out)
    alg = (p, 2, prods)

    def mul(x, y, prods=prods, p=p):
        return tuple(sum(x[i] * y[j] * prods[(i, j)][k] for i in range(2) for j in range(2)) % p
                     for k in range(2))

    def tw(x, y, mul=mul, p=p):
        # alpha(a + b eps) = a - b eps
        a = mul(x, y)
        s = mul(y, x)          # = yx; alpha(yx) = alpha(y)alpha(x) since alpha is an automorphism
        return tuple((a[k] + (1 if k == 0 else -1) * s[k]) % p for k in range(2))

    def fxy(x, y, mul=mul, p=p):
        z = mul(x, y)
        return (2 * z[0] % p, 0)     # f(a + b eps) = 2a

    print(f"--- p = {p} ---")
    print(" f(xy) equals xy + alpha(yx) on all pairs:",
          all(fxy(x, y) == tw(x, y) for x in [(a, b) for a in range(p) for b in range(p)]
              for y in [(a, b) for a in range(p) for b in range(p)]))
    determined(alg, mul, "ordinary product")
    determined(alg, tw, "twisted product")
    elts = [(a, b) for a in range(p) for b in range(p)]
    ids = [e for e in elts if mul(e, e) == e]
    print(f" idempotents: {ids}")
