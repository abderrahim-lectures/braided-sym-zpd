"""Constructors for concrete algebras in the basis e_0 = 1."""
from alg import Alg


def from_basis(p, basis, name):
    """basis: list of n tuples (each a length-n coordinate vector is circular);
    instead we accept a multiplication function on indices."""
    raise NotImplementedError


def from_mats(p, mats, name="A", one=0):
    """mats: list of n x n matrices over F_p (lists of lists), with mats[one] = identity.
    Returns Alg whose basis is mats."""
    n = len(mats)
    size = len(mats[0])
    mult = []
    for i in range(n):
        row = []
        for j in range(n):
            prod = [[sum(mats[i][a][b] * mats[j][b][c] for b in range(size)) % p
                     for c in range(size)] for a in range(size)]
            # express prod in the basis
            coords = express(p, mats, prod)
            row.append(coords)
        mult.append(row)
    return Alg(p, mult, name=name, one=one)


def express(p, mats, M):
    """Coordinates of matrix M in the basis mats (assumed to span: we just solve)."""
    n = len(mats)
    size = len(mats[0])
    # unknowns c_i with sum c_i mats[i] = M : solve by rref on the vectorised system
    rows = []
    for a in range(size):
        for b in range(size):
            rows.append([mats[i][a][b] for i in range(n)] + [M[a][b]])
    # gaussian elimination on the augmented system
    rows = [[x % p for x in r] for r in rows]
    r = 0
    piv = []
    for c in range(n):
        pivrow = -1
        for i in range(r, len(rows)):
            if rows[i][c]:
                pivrow = i
                break
        if pivrow < 0:
            continue
        rows[r], rows[pivrow] = rows[pivrow], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [(x * inv) % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    # check consistency
    for i in range(r, len(rows)):
        if all(rows[i][c] == 0 for c in range(n)) and rows[i][n] % p:
            raise ValueError("not in span")
    sol = [0] * n
    for i, c in enumerate(piv):
        sol[c] = rows[i][n]
    return sol


def full_matrix_units(p, m):
    """Basis of M_m(F_p): identity first, then the matrix units in row-major order
    (skipping the identity's units are not basis elements anyway)."""
    units = []
    for a in range(m):
        for b in range(m):
            M = [[0] * m for _ in range(m)]
            M[a][b] = 1
            units.append(M)
    ident = [[1 if a == b else 0 for b in range(m)] for a in range(m)]
    return [ident] + units


def upper_triangular_units(p, m):
    units = []
    for a in range(m):
        for b in range(m):
            if b >= a:
                M = [[0] * m for _ in range(m)]
                M[a][b] = 1
                units.append(M)
    ident = [[1 if a == b else 0 for b in range(m)] for a in range(m)]
    return [ident] + units


def product_of_fields(p, m):
    """K^m with basis u_0 = (1,...,1), u_i = E_i (i=1..m)."""
    n = m + 1
    mult = [[[0] * n for _ in range(n)] for _ in range(n)]
    # u_0 = 1
    for i in range(n):
        mult[0][i][i] = 1
        mult[i][0][i] = 1
    for i in range(1, n):
        mult[i][i][i] = 1
    return Alg(p, mult, name="K^%d" % m, one=0)
