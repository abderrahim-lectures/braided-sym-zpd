"""Fast p=2 path: tensors as bitmask ints, Gaussian elimination with ints.
Used for larger F_2 algebras (dim up to ~16).
"""
from itertools import product


def rref_bits(rows, nbits):
    """rows: list of ints (bits < nbits). Returns (pivot_positions, basis)."""
    basis = {}
    for r in rows:
        cur = r
        while cur:
            p = cur.bit_length() - 1
            if p in basis:
                cur ^= basis[p]
            else:
                basis[p] = cur
                break
    return sorted(basis), list(basis.values())


def rank_bits(rows):
    piv, _ = rref_bits(rows, 0)
    return len(piv)


def kernel_bits(mat, n):
    """mat: list of n rows (ints, bit j = coefficient of y_j) of a map F_2^n -> F_2^n.
    Returns a list of kernel vectors as ints."""
    piv = {}
    for r in mat:
        cur = r
        while cur:
            p = cur.bit_length() - 1
            if p in piv:
                cur ^= piv[p]
            else:
                piv[p] = cur
                break
    free = [j for j in range(n) if j not in piv]
    out = []
    for f in free:
        v = 1 << f
        for p in sorted(piv):          # increasing p: row p has no bits above p
            r = piv[p]
            if bin(r & v).count('1') % 2:
                v |= 1 << p
        out.append(v)
    return out


def determined2(n, MU):
    """MU[i][j] = list of n bits of mu(e_i,e_j). Returns (dimZ, dimker)."""
    # ker of mu-bar: matrix rows = output coords, columns = (i,j)
    rows = []
    for k in range(n):
        r = 0
        for i in range(n):
            for j in range(n):
                if MU[i][j][k] & 1:
                    r |= 1 << (i * n + j)
        rows.append(r)
    dimker = n * n - rank_bits([r for r in rows if r])
    gens = []
    for x in product((0, 1), repeat=n):
        if not any(x):
            continue
        # L_x: y -> mu(x,y); row k as bitmask over j
        L = []
        for k in range(n):
            r = 0
            for i in range(n):
                if not x[i]:
                    continue
                for j in range(n):
                    if MU[i][j][k] & 1:
                        r ^= 1 << j       # XOR: coefficients add in F_2
            L.append(r)
        for y in kernel_bits(L, n):
            t = 0
            for i in range(n):
                if not x[i]:
                    continue
                for j in range(n):
                    if (y >> j) & 1:
                        t |= 1 << (i * n + j)
            gens.append(t)
    dimZ = rank_bits(gens)
    return dimZ, dimker
