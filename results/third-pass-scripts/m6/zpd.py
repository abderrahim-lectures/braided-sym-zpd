"""Exact finite-field linear algebra for 'determined by a bilinear map mu'.

Everything is over F_p (p prime).  An algebra of dimension n over F_p is given by a
multiplication table T[i][j] = list of n coefficients (product e_i e_j), i,j < n.
A bilinear map mu is given the same way: MU[i][j] = vector of coefficients of mu(e_i,e_j).

determined(A, mu)  <=>  span{ x (x) y : mu(x,y) = 0 } == ker( mu-bar : A(x)A -> A )
(The inclusion span <= ker always holds; see the paper's cor:criterion and Bresar Prop 1.3.)
"""
from itertools import product


# ---------------------------------------------------------------- F_p linear algebra
def rref(rows, p, ncols=None):
    """Reduced row echelon form of a list of integer vectors mod p.
    Returns (pivot_columns, basis_rows)."""
    rows = [list(r) for r in rows]
    if ncols is None:
        ncols = len(rows[0]) if rows else 0
    pivots = []
    r = 0
    for c in range(ncols):
        # find a pivot
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c] % p, p - 2, p) if p > 2 else 1
        rows[r] = [(x * inv) % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c] % p
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
        if r == len(rows):
            break
    return pivots, rows[:r]


def rank(rows, p, ncols=None):
    return len(rref(rows, p, ncols)[0])


def kernel(mat, p, ncols=None):
    """Basis of the kernel of the linear map given by the rows of mat
    (mat[i] = image of the i-th basis vector), acting on k^ncols."""
    if ncols is None:
        ncols = len(mat[0]) if mat else 0
    if not mat:
        return [[1 if j == i else 0 for j in range(ncols)] for i in range(ncols)]
    pivots, red = rref(mat, p, ncols)
    free = [c for c in range(ncols) if c not in pivots]
    out = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for i, pc in enumerate(pivots):
            v[pc] = (-red[i][fc]) % p
        out.append(v)
    return out


# ---------------------------------------------------------------- tensors
def tensor_index(n, i, j):
    return i * n + j


def mu_matrix(n, MU):
    """Matrix of the linear map mu-bar : A(x)A -> A, as a list of n rows (output
    coordinates) each of length n*n (source coordinates indexed by (i,j))."""
    return [[MU[i][j][k] for i in range(n) for j in range(n)] for k in range(n)]


def apply_mu(n, MU, x, y):
    out = [0] * n
    for i in range(n):
        xi = x[i]
        if not xi:
            continue
        for j in range(n):
            yj = y[j]
            if not yj:
                continue
            c = (xi * yj) % p_global
            row = MU[i][j]
            for k in range(n):
                if row[k]:
                    out[k] = (out[k] + c * row[k]) % p_global
    return out


p_global = 0


def zero_product_span(n, MU, p):
    """span{ x (x) y : mu(x,y) = 0 } as a list of basis vectors in F_p^{n*n}.
    Exact: every zero pair has y in ker(mu(x,.)), so enumerating a kernel basis
    for each x enumerates the whole span."""
    global p_global
    p_global = p
    gens = []
    for x in product(range(p), repeat=n):
        if not any(x):
            continue
        # L_x : y -> mu(x,y); matrix rows = output coords k, columns = j
        L = [[0] * n for _ in range(n)]
        for i in range(n):
            if not x[i]:
                continue
            for j in range(n):
                row = MU[i][j]
                for k in range(n):
                    if row[k]:
                        L[k][j] = (L[k][j] + x[i] * row[k]) % p
        ker = kernel(L, p, n)
        for y in ker:
            t = [0] * (n * n)
            for i in range(n):
                if x[i]:
                    for j in range(n):
                        if y[j]:
                            t[tensor_index(n, i, j)] = (x[i] * y[j]) % p
            gens.append(t)
    return gens


def determined(n, MU, p):
    """(dim Z_mu, dim ker mu-bar) -- equal iff determined by mu."""
    U = mu_matrix(n, MU)
    dimker = len(kernel(U, p, n * n))
    gens = zero_product_span(n, MU, p)
    if gens:
        dimZ = rank(gens, p, n * n)
    else:
        dimZ = 0
    return dimZ, dimker


def product_mu(n, T):
    return [[list(T[i][j]) for j in range(n)] for i in range(n)]


def opp_mu(n, T):
    return [[list(T[j][i]) for j in range(n)] for i in range(n)]


def jordan_mu(n, T):
    p = None
    out = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            out[i][j] = None  # filled by caller knowing p
    return out


def jordan_mu_p(n, T, p):
    return [[[(T[i][j][k] + T[j][i][k]) % p for k in range(n)] for j in range(n)] for i in range(n)]


def compose_f_mu(fmat, n, T):
    """mu(x,y) = f(xy), f given by its matrix fmat (n x n, fmat[i] = f(e_i))."""
    MU = [[[0] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            v = list(T[i][j])
            MU[i][j] = v
    # apply f
    out = [[[0] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            v = MU[i][j]
            w = [0] * n
            for a in range(n):
                if v[a]:
                    for b in range(n):
                        w[b] += v[a] * fmat[a][b]
            out[i][j] = w
    return out


# ---------------------------------------------------------------- small algebras
def alg_matrix_units(n, p):
    """M_n(F_p), basis E_ij (i*n+j) in lexicographic order.  Returns an algebra of
    dimension N = n*n."""
    N = n * n

    def idx(a, b):
        return a * n + b
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for i in range(n):
        for j in range(n):
            for a in range(n):
                for b in range(n):
                    if j == a:
                        T[idx(i, j)][idx(a, b)][idx(i, b)] += 1
    return [[[x % p for x in T[i][j]] for j in range(N)] for i in range(N)]


def alg_upper_triangular(n, p):
    """T_n(F_p), basis E_ij with i<=j in lexicographic order."""
    pairs = [(i, j) for i in range(n) for j in range(i, n)]
    N = len(pairs)
    pos = {pr: k for k, pr in enumerate(pairs)}
    T = [[[0] * N for _ in range(N)] for _ in range(N)]
    for a, (i, j) in enumerate(pairs):
        for b, (k, l) in enumerate(pairs):
            if j == k:
                T[a][b][pos[(i, l)]] = (T[a][b][pos[(i, l)]] + 1) % p
    return T


def alg_diagonal(n, p):
    """K^n, basis of idempotents."""
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        T[i][i][i] = 1 % p
    return T


def alg_dual_numbers(p):
    """K[eps]/(eps^2), basis 1, eps."""
    T = [[[0, 0], [0, 0]] for _ in range(2)]
    T[0][0] = [1, 0]
    T[0][1] = [0, 1]
    T[1][0] = [0, 1]
    T[1][1] = [0, 0]
    return [[[x % p for x in T[i][j]] for j in range(2)] for i in range(2)]


def alg_tri(p):
    """Tri(F_p, F_p, F_p) = upper triangular 2x2 over F_p."""
    return alg_upper_triangular(2, p)


def multiply(n, T, x, y, p):
    out = [0] * n
    for i in range(n):
        if not x[i]:
            continue
        for j in range(n):
            if not y[j]:
                continue
            c = (x[i] * y[j]) % p
            row = T[i][j]
            for k in range(n):
                if row[k]:
                    out[k] = (out[k] + c * row[k]) % p
    return out


def is_associative(n, T, p):
    basis = [[1 if k == i else 0 for k in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if multiply(n, T, multiply(n, T, basis[i], basis[j], p), basis[k], p) != \
                   multiply(n, T, basis[i], multiply(n, T, basis[j], basis[k], p), p):
                    return False
    return True


def has_unit(n, T, p):
    for u in product(range(p), repeat=n):
        ok = True
        for i in range(n):
            e = [1 if k == i else 0 for k in range(n)]
            if multiply(n, T, u, e, p) != e or multiply(n, T, e, u, p) != e:
                ok = False
                break
        if ok:
            return True
    return False
