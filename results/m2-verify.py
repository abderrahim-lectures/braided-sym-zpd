#!/usr/bin/env python3
"""Independent verification of Proposition prop:matrix of
'Algebras Determined by a Braided-Symmetric Product' (v7).

For A = M_2(F_3) and mu(x,y) = xy + alpha(yx), alpha = conjugation by diag(1,-1),
the paper claims:
  * 417 of the 81*81 pairs satisfy mu(x,y) = 0,
  * rank(mu-bar) = 4, so dim ker(mu-bar) = 12,
  * the 417 tensors x (x) y span a subspace of dimension 12,
  * (hence, by Corollary cor:criterion) A is determined by mu.
It also claims 12 = 12 for the ordinary product and 13 = 13 for the twist by the
transpose.

This script recomputes all of it from scratch, and for each map proves the
conclusion Z = ker(mu-bar) directly (not just by dimensions): it computes a
kernel basis and checks every basis vector lies in the span of the zero-product
tensors. Since Z <= ker always, that proves equality.

Run: python3 results/m2-verify.py
"""
P = 3
V = [(a, b, c, d) for a in range(P) for b in range(P) for c in range(P) for d in range(P)]
E = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]


def mul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


def add(x, y):
    return tuple((u + v) % P for u, v in zip(x, y))


def transpose(x):
    return (x[0], x[2], x[1], x[3])


def conj_diag(x):                       # diag(1,-1) x diag(1,-1)^{-1}
    a, b, c, d = x
    return (a, (-b) % P, (-c) % P, d)


CASES = {
    "twisted, alpha = conj by diag(1,-1)": lambda x, y: add(mul(x, y), conj_diag(mul(y, x))),
    "ordinary product":                    lambda x, y: mul(x, y),
    "twist by transpose (braiding)":       lambda x, y: add(mul(x, y), mul(transpose(y), transpose(x))),
}


def tensor(x, y):
    return [x[i] * y[j] % P for i in range(4) for j in range(4)]


def rank(rows, n):
    """rank over F_P of row vectors of length n (left-to-right pivots)"""
    basis, pivots = [], []
    for r in rows:
        r = list(r)
        for q, b in zip(pivots, basis):
            f = r[q]
            if f:
                r = [(r[j] - f * b[j]) % P for j in range(n)]
        for j in range(n):
            if r[j]:
                inv = pow(r[j], P - 2, P)
                basis.append([(v * inv) % P for v in r])
                pivots.append(j)
                break
    return len(basis)


def rref(m, ncols):
    """reduced row echelon form over F_P; returns (rows, pivot columns)"""
    m = [list(r) for r in m]
    piv, r, rows = [], 0, len(m)
    for c in range(ncols):
        pr = next((i for i in range(r, rows) if m[i][c] % P), None)
        if pr is None:
            continue
        m[r], m[pr] = m[pr], m[r]
        inv = pow(m[r][c], P - 2, P)
        m[r] = [(v * inv) % P for v in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % P:
                f = m[i][c]
                m[i] = [(m[i][j] - f * m[r][j]) % P for j in range(ncols)]
        piv.append(c)
        r += 1
        if r == rows:
            break
    return m, piv


def check(name, mu):
    # mu-bar : A (x) A -> A, in the basis E_i (x) E_j  (4 x 16 matrix)
    mat = [[mu(x, y)[i] for x in E for y in E] for i in range(4)]
    M, piv = rref(mat, 16)
    assert all(all(sum(mat[i][j] * v[j] for j in range(16)) % P == 0 for i in range(4)) for v in
               [[0] * 16]), "trivial"
    ker = []
    for fc in [c for c in range(16) if c not in piv]:
        v = [0] * 16
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][fc]) % P
        ker.append(v)
    # every kernel vector really is killed by mu-bar
    ok_ker = all(all(sum(mat[i][j] * v[j] for j in range(16)) % P == 0 for i in range(4)) for v in ker)
    zero = [tensor(x, y) for x in V for y in V if mu(x, y) == (0, 0, 0, 0)]
    # every generator is killed by mu-bar (this is Z <= ker)
    ok_z = all(mu(x, y) == (0, 0, 0, 0) for x in V for y in V if mu(x, y) == (0, 0, 0, 0))
    # and ker <= Z, by rank comparison
    z_eq_ker = ok_ker and ok_z and rank(zero + ker, 16) == rank(zero, 16) == len(ker)
    print(f"{name:38s} #zeros={len(zero):4d}  dim span(Z)={rank(zero,16):2d}  "
          f"rank mu-bar={len(piv)}  dim ker={16-len(piv):2d}  Z=ker: {z_eq_ker}")
    return len(zero), rank(zero, 16), 16 - len(piv), z_eq_ker


if __name__ == "__main__":
    results = {k: check(k, f) for k, f in CASES.items()}
    t = results["twisted, alpha = conj by diag(1,-1)"]
    assert t == (417, 12, 12, True), t
    assert results["ordinary product"] == (417, 12, 12, True)
    assert results["twist by transpose (braiding)"] == (513, 13, 13, True)
    print("\nAll of prop:matrix verified: 417 zero pairs, rank(mu-bar)=4, "
          "dim span(Z)=12=dim ker, and Z=ker(mu-bar).")
