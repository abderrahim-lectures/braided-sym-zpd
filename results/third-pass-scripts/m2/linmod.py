"""Linear algebra over F_p and finite-dimensional algebra utilities.

An algebra is given by p (prime) and mult, where mult[i][j] is the coefficient
vector (length n) of e_i * e_j in the basis e_0=1, e_1, ..., e_{n-1}.
"""


def rref(rows, p):
    """Reduced row echelon form over F_p.  Returns (M, pivots)."""
    M = [[x % p for x in r] for r in rows]
    if not M:
        return M, []
    ncols = len(M[0])
    piv = []
    r = 0
    for c in range(ncols):
        pivot = -1
        for i in range(r, len(M)):
            if M[i][c]:
                pivot = i
                break
        if pivot < 0:
            continue
        M[r], M[pivot] = M[pivot], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    return M, piv


def nullspace(rows, p, ncols):
    """Basis of {x in F_p^ncols : rows . x = 0}, as a list of lists."""
    M, piv = rref(rows, p) if rows else ([], [])
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [0] * ncols
        v[f] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][f]) % p
        basis.append(v)
    return basis


def span_basis(vecs, p, n):
    """Basis of the span of a list of vectors in F_p^n."""
    M, piv = rref(vecs, p) if vecs else ([], [])
    return [M[i] for i in range(len(piv))]


def rank(vecs, p, n):
    return len(span_basis(vecs, p, n))


def annihilator(vecs, p, n):
    """Basis of the functionals lambda (length n) with lambda(v) = 0 for all
    v in span(vecs).  Vectors themselves are the rows."""
    rows = [[v[k] for k in range(n)] for v in vecs]
    return nullspace(rows, p, n)


def make_tab(mult, p):
    """mult[i][j] coefficient list -> tab[(i,j)] as tuple.  Also return n."""
    n = len(mult)
    tab = {}
    for i in range(n):
        for j in range(n):
            tab[i, j] = tuple(x % p for x in mult[i][j])
    return tab, n
