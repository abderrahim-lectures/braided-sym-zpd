"""m5: further checks around rem:inner, thm:zpd-fxy, thm:codim and q:noncomm.

1. rem:inner, "the answer does not depend on D": for every invertible D in
   M_2(F_3), alpha = conj by D, compute dim Zs and dim ker of bar-mu_alpha.
2. q:noncomm, "the question is therefore about algebras admitting an involutive
   automorphism that is not inner": in characteristic 2 the inner case is not
   covered by rem:inner (which assumes char != 2).  Test M_2(F_2) with the
   Jordan product x o y = xy + yx: is it determined?
3. thm:zpd-fxy and thm:codim: brute-force check on small examples.
4. cor:identity, part (ii): char 2, mu = 2xy = 0, everything determined.

Run: python3 m5-checks.py
"""
import itertools

# ---------------------------------------------------------------- generic F_p algebra


class Alg:
    def __init__(self, p, n, mult):
        self.p, self.n, self.mult = p, n, mult   # mult: n x n table of tuples

    def mul(self, a, b):
        return tuple(sum(a[i] * b[j] * self.mult[(i, j)][k] for i in range(self.n)
                         for j in range(self.n)) % self.p for k in range(self.n))


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


def determined(alg, mu, label, verbose=True):
    """Is dim Zs_mu == dim ker bar-mu ?  (cor:criterion)"""
    p, n = alg.p, alg.n
    elts = [tuple(v) for v in itertools.product(range(p), repeat=n)]
    # matrix of bar-mu on basis e_i (x) e_j
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
        print(f"  [{label}] #{'':0}{len(tens)} zero pairs; rank bar-mu = {rk}; "
              f"dim ker = {n*n-rk}; dim Zs = {dz}; determined = {ok}")
    return ok, len(tens), rk, n * n - rk, dz


# ---------------------------------------------------------------- M_2(F_p)
def mat_alg(p):
    def mult(i, j):           # matrix units E_i, E_j with indices 0..3 = (0,0),(0,1),(1,0),(1,1)
        E = {}
        for a in range(2):
            for b in range(2):
                E[(a, b)] = a * 2 + b
        rows = [(0, 0), (0, 1), (1, 0), (1, 1)]
        (a, b), (c, d) = rows[i], rows[j]
        out = [0, 0, 0, 0]
        if b == c:
            out[E[(a, d)]] = 1
        return tuple(out)
    return Alg(p, 4, {(i, j): mult(i, j) for i in range(4) for j in range(4)})


def mm(X, Y, p):
    return [[(X[0][0] * Y[0][0] + X[0][1] * Y[1][0]) % p,
             (X[0][0] * Y[0][1] + X[0][1] * Y[1][1]) % p],
            [(X[1][0] * Y[0][0] + X[1][1] * Y[1][0]) % p,
             (X[1][0] * Y[0][1] + X[1][1] * Y[1][1]) % p]]


def flat(M):
    return tuple(M[i][j] for i in range(2) for j in range(2))


print("=== 1. rem:inner: independence of D, alpha = conjugation by D, M_2(F_3) ===")
p = 3
invertible = []
allm = [[[a, b], [c, d]] for a in range(p) for b in range(p) for c in range(p) for d in range(p)]
for D in allm:
    det = (D[0][0] * D[1][1] - D[0][1] * D[1][0]) % p
    if det:
        invertible.append(D)
print("  #invertible D in M_2(F_3):", len(invertible))


def inv2(D, p):
    det = (D[0][0] * D[1][1] - D[0][1] * D[1][0]) % p
    di = pow(det, -1, p)
    return [[D[1][1] * di % p, (-D[0][1]) * di % p],
            [(-D[1][0]) * di % p, D[0][0] * di % p]]


alg = mat_alg(3)
sigs = set()
for D in invertible:
    Di = inv2(D, p)

    def mu(x, y, D=D, Di=Di):
        X = [[x[0], x[1]], [x[2], x[3]]]
        Y = [[y[0], y[1]], [y[2], y[3]]]
        t = mm(mm(D, mm(Y, X, p), p), Di, p)
        return flat(mm(X, Y, p)) if False else tuple(
            (mm(X, Y, p)[i][j] + t[i][j]) % p for i in range(2) for j in range(2))
    ok, nz, rk, dk, dz = determined(alg, mu, f"D={D}", verbose=False)
    sigs.add((rk, dk, dz, ok))
    print(f"  D={D}: rank={rk} dimker={dk} dimZs={dz} determined={ok}")
print("  distinct (rank, dim ker, dim Zs, determined):", sigs)

print("\n=== 2. q:noncomm: M_2(F_2) with the Jordan product (char 2) ===")
p2 = 2
alg2 = mat_alg(2)


def jordan2(x, y):
    X = [[x[0], x[1]], [x[2], x[3]]]
    Y = [[y[0], y[1]], [y[2], y[3]]]
    A = mm(X, Y, p2)
    B = mm(Y, X, p2)
    return tuple((A[i][j] + B[i][j]) % p2 for i in range(2) for j in range(2))


determined(alg2, jordan2, "M_2(F_2), x o y = xy+yx")
print("  (in char 2, x o x = 0 for every x, so the diagonal pairs are all 'zero pairs')")

print("\n=== 2b. M_2(F_3) with the Jordan product (char != 2) ===")
determined(mat_alg(3), lambda x, y: jordan2(x, y), "M_2(F_3), x o y = xy+yx") if False else None
p3 = 3


def jordan3(x, y):
    X = [[x[0], x[1]], [x[2], x[3]]]
    Y = [[y[0], y[1]], [y[2], y[3]]]
    A = mm(X, Y, p3)
    B = mm(Y, X, p3)
    return tuple((A[i][j] + B[i][j]) % p3 for i in range(2) for j in range(2))


determined(mat_alg(3), jordan3, "M_2(F_3), x o y = xy+yx")

print("\n=== 3a. thm:zpd-fxy: A = F_3 x F_3 (zpd), mu = f(xy) for every linear f ===")
p = 3
n = 2
# A = F x F, multiplication componentwise, e0 = (1,0), e1 = (0,1)
mult = {}
for i in range(n):
    for j in range(n):
        out = [0] * n
        if i == j:
            out[i] = 1
        mult[(i, j)] = tuple(out)
algFF = Alg(p, 2, mult)
fails = 0
tested = 0
for a in itertools.product(range(p), repeat=n * n):
    f = [a[0:2], a[2:4]]   # f(e_j) = column j

    def mu(x, y, f=f):
        xy = algFF.mul(x, y)
        return tuple(sum(f[k][i] * xy[i] for i in range(n)) % p for k in range(n))
    ok, *_ = determined(algFF, mu, "", verbose=False)
    tested += 1
    if not ok:
        fails += 1
print(f"  tested {tested} linear f on F_3 x F_3: determined in {tested-fails} cases, failed in {fails}")

print("\n=== 3b. thm:codim on A = F_3[t]/(t^3), f = constant term ===")


def poly_mul(x, y):
    c = [0, 0, 0]
    for i in range(3):
        for j in range(3):
            if i + j < 3:
                c[i + j] = (c[i + j] + x[i] * y[j]) % p
    return tuple(c)


multi = {}
for i in range(3):
    for j in range(3):
        e = [0, 0, 0]
        e[i] = 1
        multi[(i, j)] = poly_mul(e, e and tuple(1 if k == j else 0 for k in range(3)))
algP = Alg(p, 3, multi)


def mu_const(x, y):
    xy = algP.mul(x, y)
    return (xy[0], 0, 0)


determined(algP, mu_const, "F_3[t]/(t^3), mu = const term of xy")

print("\n=== 4. cor:identity in char 2: mu = 2xy = 0, every algebra determined ===")
zero_mu = {}
alg2b = mat_alg(2)
determined(alg2b, lambda x, y: (0, 0, 0, 0), "M_2(F_2), mu = 0")
