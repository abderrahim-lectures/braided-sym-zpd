"""Exact linear algebra for bilinear maps mu: A x A -> A over a field F.

A is F^n with basis e_0..e_{n-1}; tensors A (x) A have basis e_i (x) e_j ordered
(i,j) -> i*n + j.  Z_mu is the span of the elementary tensors e_i (x) e_j with
mu(e_i,e_j) = 0; ker mu_bar is the kernel of the n x n^2 matrix of mu_bar.
By Bresar Prop 1.3(iii) / Brice-Huang Thm 2.3, (A,mu) is zpd ("A determined by
mu") iff Z_mu = ker mu_bar.

Fields are given by a prime p (F_p) or p = 0 (Q, using Fractions).
"""
from fractions import Fraction


class Field:
    def __init__(self, p):
        self.p = p          # 0 means Q
        self.zero = 0 if p else Fraction(0)
        self.one = 1 if p else Fraction(1)

    def elt(self, a):
        if self.p:
            return a % self.p
        return Fraction(a)

    def add(self, a, b):
        if self.p:
            return (a + b) % self.p
        return a + b

    def sub(self, a, b):
        if self.p:
            return (a - b) % self.p
        return a - b

    def mul(self, a, b):
        if self.p:
            return (a * b) % self.p
        return a * b

    def div(self, a, b):
        if self.p:
            return (a * pow(b, -1, self.p)) % self.p
        return a / b

    def neg(self, a):
        return self.sub(self.zero, a)

    def is_zero(self, a):
        return a == self.zero

    def name(self):
        return "Q" if not self.p else "F_%d" % self.p


def mat_rank(F, rows):
    """rank of a list of row vectors over F (exact)."""
    rows = [list(r) for r in rows]
    if not rows:
        return 0
    m, n = len(rows), len(rows[0])
    rank = 0
    for col in range(n):
        piv = None
        for i in range(rank, m):
            if not F.is_zero(rows[i][col]):
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = F.div(F.one, rows[rank][col])
        rows[rank] = [F.mul(inv, x) for x in rows[rank]]
        for i in range(m):
            if i != rank and not F.is_zero(rows[i][col]):
                fac = rows[i][col]
                rows[i] = [F.sub(rows[i][k], F.mul(fac, rows[rank][k]))
                           for k in range(n)]
        rank += 1
        if rank == m:
            break
    return rank


def span_dim(F, vectors, dim):
    return mat_rank(F, vectors)


def kernel_dim(F, matrix, ncols):
    """dim ker of the linear map given by `matrix` (list of rows)."""
    return ncols - mat_rank(F, matrix)


def mu_matrix(F, n, mu):
    """n x n^2 matrix of mu_bar in the bases fixed above."""
    rows = []
    for a in range(n):
        row = []
        for i in range(n):
            for j in range(n):
                row.append(mu[i][j][a])
        rows.append(row)
    return rows


def Z_mu(F, n, mu):
    """list of tensors e_i (x) e_j with mu(e_i,e_j)=0 (spanning set of Z_mu)."""
    vecs = []
    for i in range(n):
        for j in range(n):
            if all(F.is_zero(mu[a][i][j]) for a in range(n)):
                v = [F.zero] * (n * n)
                v[i * n + j] = F.one
                vecs.append(v)
    return vecs


def report(F, name, n, mu):
    M = mu_matrix(F, n, mu)
    dker = kernel_dim(F, M, n * n)
    Z = Z_mu(F, n, mu)
    dz = span_dim(F, Z, n * n)
    # also check Z subset ker(mu_bar): every generating tensor must be in ker
    in_kernel = True
    for v in Z:
        img = [sum((F.mul(M[a][k], v[k]) for k in range(n * n)), F.zero)
               for a in range(n)]
        if any(not F.is_zero(x) for x in img):
            in_kernel = False
    return {"name": name, "field": F.name(), "dim ker mu_bar": dker,
            "dim Z_mu": dz, "determined": dker == dz and in_kernel,
            "Z in ker": in_kernel}


# ---------------------------------------------------------------- products

def rank_one(F, n, lam, a):
    """mu(x,y) = lam(x) lam(y) a."""
    mu = [[[F.mul(F.mul(lam[i], lam[j]), a[k]) for k in range(n)]
           for j in range(n)] for i in range(n)]
    return mu


def from_struct(F, n, table):
    """table[i][j] = list of n coefficients of e_i e_j."""
    return [[[F.elt(table[i][j][k]) for k in range(n)] for j in range(n)]
            for i in range(n)]


def unital_product(F, n):
    """associative unital product on F^n with unit e_0 and e_i e_j = delta_ij e_i
    for i,j >= 1 (so A = F x F^{n-1}, a product of copies of F)."""
    mu = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        mu[0][i][i] = F.one
        mu[i][0][i] = F.one
    for i in range(1, n):
        for j in range(1, n):
            if i == j:
                mu[i][j][i] = F.one
    return mu


def compose(F, n, f, mu):
    """(f o mu)(x,y) = f(mu(x,y))."""
    out = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    out[i][j][k] = F.add(out[i][j][k],
                                         F.mul(f[k][l], mu[i][j][l]))
    return out


def jordan(F, n, mu):
    out = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                out[i][j][k] = F.add(mu[i][j][k], mu[j][i][k])
    return out
