#!/usr/bin/env python3
"""m2 / Task C: check the numbers asserted in prose of paper/braided-sym-zpd.tex.

  prop:matrix  : 81*81 pairs, 417 zero pairs, rank mu-bar = 4, dim ker = 12,
                 the 417 tensors span a 12-dimensional subspace.
  prose after  : "dim Zs = dim ker = 12 for the ordinary product" and
                 "13 = 13 for the twist by the transpose ... xy + y^T x^T".

Everything is exact: A = M_2(F_3) has 4^4 = 256 elements, A (x) A is 16-dimensional
over F_3, so Gaussian elimination is done in F_3 with integers mod 3.
"""
from itertools import product

p = 3
I2 = (1, 0, 0, 1)


def mul(x, y, p=p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p,
            (c * e + d * g) % p, (c * f + d * h) % p)


def add(x, y, p=p):
    return tuple((u + v) % p for u, v in zip(x, y))


def neg(x, p=p):
    return tuple((-u) % p for u in x)


def tr(x):
    a, b, c, d = x
    return (a, c, b, d)


def scal(k, x, p=p):
    return tuple((k * u) % p for u in x)


D = (1, 0, 0, p - 1)          # diag(1,-1)
Dinv = (1, 0, 0, p - 1)       # = D, since D^2 = 1


def conj(x):                   # alpha(x) = D x D^{-1}
    return mul(mul(D, x), Dinv)


BASIS = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
ELEMS = list(product(range(p), repeat=4))


def rank(rows, p=p):
    rows = [list(r) for r in rows]
    r = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], -1, p)
        rows[r] = [(v * inv) % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(u - f * v) % p for u, v in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def analyse(name, mu):
    # matrix of mu-bar in the basis E_i (x) E_j  (16 columns, 4 rows)
    cols = [mu(BASIS[i], BASIS[j]) for i in range(4) for j in range(4)]
    mat = [[cols[k][r] % p for k in range(16)] for r in range(4)]
    rk = rank(mat)
    zeros, tens = 0, []
    for x in ELEMS:
        for y in ELEMS:
            if mu(x, y) == (0, 0, 0, 0):
                zeros += 1
                # coordinates of x (x) y in the basis E_i (x) E_j
                t = [0] * 16
                for i in range(4):
                    for j in range(4):
                        t[4 * i + j] = (x[i] * y[j]) % p
                tens.append(t)
    span = rank(tens) if tens else 0
    print("%-38s  rank(mu-bar)=%2d  dim ker=%2d  zero pairs=%4d  dim span=%2d  %s"
          % (name, rk, 16 - rk, zeros, span, "EQUAL" if span == 16 - rk else "DIFFER"))
    return rk, 16 - rk, zeros, span


print("A = M_2(F_3), dim A = 4, dim A(x)A = 16\n")
analyse("mu = xy              (ordinary product)", lambda x, y: mul(x, y))
analyse("mu = 2xy             (identity braiding)", lambda x, y: add(mul(x, y), mul(x, y)))
analyse("mu = xy + yx         (swap / Jordan)", lambda x, y: add(mul(x, y), mul(y, x)))
analyse("mu = xy + a(y)a(x)   (alpha = conj diag(1,-1))",
        lambda x, y: add(mul(x, y), mul(conj(y), conj(x))))
analyse("mu = xy + a(yx)      (same, alpha automorphism)",
        lambda x, y: add(mul(x, y), conj(mul(y, x))))
analyse("mu = xy + y^T x^T    (transpose twist)",
        lambda x, y: add(mul(x, y), mul(tr(y), tr(x))))
analyse("mu = xy + (xy)^T     (same, rewritten)",
        lambda x, y: add(mul(x, y), tr(mul(x, y))))

# sanity: alpha really is an involution and an automorphism
print("\nalpha = conj by diag(1,-1): alpha^2 = id ->",
      all(conj(conj(x)) == x for x in ELEMS),
      "; alpha(xy) = alpha(x)alpha(y) ->",
      all(conj(mul(x, y)) == mul(conj(x), conj(y)) for x in ELEMS for y in ELEMS))
