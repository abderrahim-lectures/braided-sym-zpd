"""Checks for the novelty audit of paper/braided-sym-zpd.tex (v8).  (fixed)

Z_mu = span{x (x) y : mu(x,y) = 0} must range over ALL pairs, not only basis
pairs.  Over F_p we enumerate all p^(2n) pairs (exact).  Over Q we sample a
grid and use the dimension sandwich
      Z_found <= Z_mu <= ker mu_bar
so dim Z_found = dim ker mu_bar proves equality (a rigorous check).

(1) rank-one lemma: (A, mu) with mu(x,y) = lambda(x)lambda(y)a is determined
    (thm:codim's hypotheses force exactly this shape: mu = c(x)c(y)f(1)).
(2) ex:dual is the rank-one instance lambda = c, a = 1, f = id + alpha.
(3) M_2(F_3) ordinary product and prop:matrix product (paper: 12 = 12).
(4) general lemma: (A,mu) zpd with mu_bar onto => (A, f o mu) determined for
    every linear f; instance mu = Jordan product on K x K, mu != m.
"""
from itertools import product
from zpd_tools import Field, mu_matrix, mat_rank, kernel_dim

out = []


def say(*a):
    s = " ".join(str(x) for x in a)
    out.append(s)
    print(s)


def zeros(F, n):
    return [F.zero] * n


def is_zero_vec(v):
    return all(c == 0 for c in v)


def mul_vec(F, mu, x, y, n):
    r = [F.zero] * n
    for k in range(n):
        s = F.zero
        for i in range(n):
            if x[i] == 0:
                continue
            for j in range(n):
                if y[j] == 0:
                    continue
                s = F.add(s, F.mul(x[i], F.mul(y[j], mu[i][j][k])))
        r[k] = s
    return r


def all_vectors(F, n, grid=None):
    if F.p:
        return [list(v) for v in product(range(F.p), repeat=n)]
    return [list(v) for v in product(grid, repeat=n)]


def dim_Z(F, n, mu, grid=None):
    vecs = []
    vs = all_vectors(F, n, grid)
    for x in vs:
        for y in vs:
            if is_zero_vec(mul_vec(F, mu, x, y, n)):
                t = []
                for i in range(n):
                    for j in range(n):
                        t.append(F.mul(x[i], y[j]))
                vecs.append(t)
    return mat_rank(F, vecs), len(vs) ** 2


def dim_ker(F, n, mu):
    return kernel_dim(F, mu_matrix(F, n, mu), n * n)


def check(F, n, mu, label, grid=None, quiet=False):
    dz, npairs = dim_Z(F, n, mu, grid)
    dk = dim_ker(F, n, mu)
    if not quiet:
        say("    %-46s %-4s dim Z=%2d dim ker mu_bar=%2d determined=%s   (pairs %d)"
            % (label, F.name(), dz, dk, dz == dk, npairs))
    return dz == dk


# ------------------------------------------------------------------ products
def rank_one(F, n, lam, a):
    return [[[F.mul(F.mul(lam[i], lam[j]), a[k]) for k in range(n)]
             for j in range(n)] for i in range(n)]


def dual_numbers(F):
    n = 2
    m = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    m[0][0][0] = F.one
    m[0][1][1] = F.one
    m[1][0][1] = F.one
    return m


def twist(F, m, alpha):
    n = len(m)
    out = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                s = m[i][j][k]
                for b in range(n):
                    if alpha[j][b] == 0:
                        continue
                    for c in range(n):
                        if alpha[i][c] == 0:
                            continue
                        s = F.add(s, F.mul(alpha[j][b],
                                           F.mul(alpha[i][c], m[b][c][k])))
                out[i][j][k] = s
    return out


def compose(F, n, f, mu):
    out = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                s = F.zero
                for l in range(n):
                    if f[k][l] == 0:
                        continue
                    s = F.add(s, F.mul(f[k][l], mu[i][j][l]))
                out[i][j][k] = s
    return out


def jordan(F, m):
    n = len(m)
    return [[[F.add(m[i][j][k], m[j][i][k]) for k in range(n)]
             for j in range(n)] for i in range(n)]


def kxk_product(F, n):
    mu = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        mu[i][i][i] = F.one
    return mu


# ============================================================ (1) rank one
say("== (1) rank-one products mu(x,y) = lambda(x)lambda(y)a : always determined ==")
for p, ns in [(2, [2, 3, 4]), (3, [2, 3]), (5, [2, 3]), (0, [2, 3])]:
    F = Field(p)
    for n in ns:
        lams = []
        for i in range(n):
            v = [F.zero] * n
            v[i] = F.one
            lams.append(("e%d^*" % i, v))
        lams.append(("ones", [F.one] * n))
        if n >= 2:
            v = [F.zero] * n
            v[0] = F.one
            v[1] = F.one
            lams.append(("e0^*+e1^*", v))
        lams.append(("zero", [F.zero] * n))
        okall = True
        for name, lam in lams:
            for ai in range(n):
                a = [F.zero] * n
                a[ai] = F.one
                mu = rank_one(F, n, lam, a)
                if not check(F, n, mu, "rank-one lam=%s a=e%d" % (name, ai),
                             grid=[0, 1, -1]):
                    okall = False
        say("  %-4s n=%d all rank-one products determined: %s"
            % (F.name(), n, okall))

# ============================================================ (2) dual numbers
say("")
say("== (2) ex:dual: A=K[eps]/eps^2, alpha(a+b eps)=a-b eps, mu_alpha(x,y)=xy+alpha(y)alpha(x) ==")
for p in [0, 3, 5]:
    F = Field(p)
    m = dual_numbers(F)
    alpha = [[F.one, F.zero], [F.zero, F.sub(F.zero, F.one)]]
    mu = twist(F, m, alpha)
    c = [F.one, F.zero]
    twoc = F.add(F.one, F.one)
    shape = True
    for i in range(2):
        for j in range(2):
            for k in range(2):
                want = F.mul(F.mul(twoc, F.mul(c[i], c[j])),
                             F.one if k == 0 else F.zero)
                if mu[i][j][k] != want:
                    shape = False
    say("  %-4s mu_alpha = 2c(x)c(y)e0 : %s" % (F.name(), shape))
    check(F, 2, m, "ordinary product (zpd?)", grid=[0, 1])
    check(F, 2, mu, "twisted product (determined?)", grid=[0, 1])

# ============================================================ (3) M_2(F_3)
say("")
say("== (3) M_2(F_3): ordinary product and prop:matrix product ==")
F = Field(3)
n = 4
def unit(i, j):
    v = [F.zero] * n
    v[i * 2 + j] = F.one
    return v
def mat_mul(u, w):
    res = [F.zero] * n
    for i in range(2):
        for j in range(2):
            s = F.zero
            for k in range(2):
                s = F.add(s, F.mul(u[i * 2 + k], w[k * 2 + j]))
            res[i * 2 + j] = s
    return res
base = [unit(i, j) for i in range(2) for j in range(2)]
m = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
for i in range(n):
    for j in range(n):
        m[i][j] = mat_mul(base[i], base[j])
check(F, n, m, "ordinary product", grid=None)
def conj(u):
    res = [F.zero] * n
    d = [F.one, F.sub(F.zero, F.one)]
    for i in range(2):
        for j in range(2):
            res[i * 2 + j] = F.mul(u[i * 2 + j], F.div(d[i], d[j]))
    return res
mu = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
for i in range(n):
    for j in range(n):
        yx = mat_mul(base[j], base[i])
        ayx = conj(yx)
        mu[i][j] = [F.add(m[i][j][k], ayx[k]) for k in range(n)]
check(F, n, mu, "mu_alpha(x,y)=xy+alpha(yx), alpha=conj diag(1,-1)")

# ================================================== (4) general lemma instance
say("")
say("== (4) general lemma: (A,mu) zpd + mu_bar onto => (A, f o mu) determined ==")
for p in [0, 3, 5]:
    F = Field(p)
    n = 2
    m = kxk_product(F, n)          # A = K x K
    muJ = jordan(F, m)             # x o y = 2xy, onto in char != 2
    rank = mat_rank(F, mu_matrix(F, n, muJ))
    r0 = check(F, n, muJ, "Jordan product on K x K", grid=[0, 1, -1])
    allok = True
    nf = 0
    vals = range(p) if p else [0, 1, -1, 2]
    for e in product(vals, repeat=4):
        f = [[F.elt(e[0]), F.elt(e[1])], [F.elt(e[2]), F.elt(e[3])]]
        mu2 = compose(F, n, f, muJ)
        dz, _ = dim_Z(F, n, mu2, grid=[0, 1, -1, 2, -2])
        dk = dim_ker(F, n, mu2)
        nf += 1
        if dz != dk:
            allok = False
            say("    FAILS for f=%s (dim Z=%d, dim ker=%d)" % (f, dz, dk))
    say("  %-4s rank mu_bar=%d (=dim A: %s); (A,muJ) determined=%s; (A, f o muJ) determined for all %d linear f: %s"
        % (F.name(), rank, rank == n, r0, nf, allok))

open("novelty_checks.txt", "w").write("\n".join(out) + "\n")
