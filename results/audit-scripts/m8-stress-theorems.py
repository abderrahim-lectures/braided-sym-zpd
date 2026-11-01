#!/usr/bin/env python3
"""Brute-force stress tests of the paper's own theorems (Section 4-5).

1. thm:zpd-fxy (4.1): for EVERY linear f on a unital zpd algebra A, is A determined
   by mu(x,y) = f(xy)?  Checked exhaustively for A = F_3 x F_3 and A = T_2(F_3)
   (both zpd), against Bresar's criterion dim Zs = dim ker.
2. thm:codim (5.1): A = F_3 + V with V^2 = 0, dim V = 2 (not zpd); f = projection
   onto the F_3-summand.  The hypotheses of 5.1 hold (N = V is an ideal of
   codimension 1, f(1) = 1 != 0); check that A is determined by mu(x,y)=f(xy).
3. prop:injective (4.2): A = F_3[eps] (not zpd), f injective => NOT determined.
4. consistency check only: over a finite field EVERY quaternion algebra is split
   (a nondegenerate 4-dimensional quadratic form over F_q, q odd, is isotropic), so
   the computation below checks M_2(F_3) again and says nothing about Bresar's
   Example 3.19 over R, which is verified from the book's proof instead.
"""
import itertools
import numpy as np


def rref_rank(rows, p):
    if not rows:
        return 0
    M = np.array(rows, dtype=np.int64) % p
    nr, nc = M.shape
    r = 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if M[i, c] % p), None)
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        M[r] = (M[r] * pow(int(M[r, c]) % p, p - 2, p)) % p
        for i in range(nr):
            if i != r and M[i, c] % p:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
        if r == nr:
            break
    return r


def determined(mu, n, p):
    """True iff dim Zs_mu = dim ker mu-bar (Bresar Prop 1.3)."""
    cols = []
    for i in range(n):
        for j in range(n):
            ei = [0] * n
            ei[i] = 1
            ej = [0] * n
            ej[j] = 1
            cols.append([c % p for c in mu(ei, ej)])
    rows = [[cols[c][k] for c in range(n * n)] for k in range(n)]
    dimker = n * n - rref_rank(rows, p)
    tens = []
    for x in itertools.product(range(p), repeat=n):
        for y in itertools.product(range(p), repeat=n):
            if not any(c % p for c in mu(list(x), list(y))):
                v = [0] * (n * n)
                for i in range(n):
                    for j in range(n):
                        v[i * n + j] = x[i] * y[j] % p
                tens.append(v)
    return dimker == rref_rank(tens, p), dimker, rref_rank(tens, p)


def main():
    p = 3
    print("== 1. thm:zpd-fxy over every linear f ==")
    # A = F_3 x F_3
    tab = [[[1, 0], [0, 0]], [[0, 0], [0, 1]]]

    def mul_kk(x, y):
        return [sum(x[i] * y[j] * tab[i][j][k] for i in range(2) for j in range(2)) % p for k in range(2)]

    bad = 0
    for entries in itertools.product(range(p), repeat=4):
        f = lambda z, M=entries: [(M[0] * z[0] + M[1] * z[1]) % p, (M[2] * z[0] + M[3] * z[1]) % p]
        ok, dk, dz = determined(lambda x, y: f(mul_kk(x, y)), 2, p)
        if not ok:
            bad += 1
            print("   counterexample f =", entries, dk, dz)
    print(f"   A = F_3 x F_3 (zpd): {3**4} linear maps f, failures = {bad}")

    # A = T_2(F_3)
    I, E12, J = [1, 0, 0], [0, 1, 0], [0, 0, 1]

    def mul_T(x, y):
        a, b, c = x
        a2, b2, c2 = y
        return [a * a2 % p, (a * b2 + b * c2) % p, c * c2 % p]

    bad = 0
    tested = 0
    for entries in itertools.product(range(p), repeat=9):
        def f(z, M=entries):
            return [sum(M[3 * i + j] * z[j] for j in range(3)) % p for i in range(3)]
        ok, dk, dz = determined(lambda x, y: f(mul_T(x, y)), 3, p)
        tested += 1
        if not ok:
            bad += 1
            if bad < 4:
                print("   counterexample f =", entries, dk, dz)
    print(f"   A = T_2(F_3) (zpd): {tested} linear maps f, failures = {bad}")

    print()
    print("== 2. thm:codim on A = F_3 + V, dim V = 2, V^2 = 0 (not zpd) ==")
    n = 3  # basis 1, v1, v2 ;  V*V = 0  so (a+v)(c+w) = ac + aw + cv
    def mul_R(x, y):
        return [x[0] * y[0] % p,
                (x[0] * y[1] + y[0] * x[1]) % p,
                (x[0] * y[2] + y[0] * x[2]) % p]
    f = lambda z: [z[0] % p, 0, 0]      # projection onto the F_3-summand
    print("   f(1) != 0:", f([1, 0, 0]) != [0, 0, 0], " N = ker f = V is an ideal of codim 1")
    ok, dk, dz = determined(lambda x, y: f(mul_R(x, y)), n, p)
    print(f"   determined by mu(x,y)=f(xy): {ok}  (dim ker = {dk}, dim Zs = {dz})")
    okz, dkz, dzz = determined(mul_R, n, p)
    print(f"   zpd?  {okz}  (dim ker = {dkz}, dim Zs = {dzz})")

    print()
    print("== 3. prop:injective: A = F_3[eps], f injective (f(a+beps)=a+2b eps) ==")
    def mul_d(x, y):
        return [x[0] * y[0] % p, (x[0] * y[1] + x[1] * y[0]) % p]
    f = lambda z: [z[0] % p, 2 * z[1] % p]
    ok, dk, dz = determined(lambda x, y: f(mul_d(x, y)), 2, p)
    print(f"   injective f: determined = {ok} (dim ker = {dk}, dim Zs = {dz}); A zpd = "
          f"{determined(mul_d, 2, p)[0]}")

    print()
    print("== 4. quaternion algebra over F_3 (split), alpha = id: zJpd? ==")
    # basis 1, i, j, k ; i^2 = j^2 = k^2 = -1 ; ij = k, jk = i, ki = j, ji = -k, ...
    qtab = {}
    def qmul(u, v):
        # unit quaternion multiplication table, u,v in {0:1,1:i,2:j,3:k}
        table = {
            (0, 0): (1, 0), (0, 1): (1, 1), (0, 2): (1, 2), (0, 3): (1, 3),
            (1, 0): (1, 1), (2, 0): (1, 2), (3, 0): (1, 3),
            (1, 1): (-1, 0), (2, 2): (-1, 0), (3, 3): (-1, 0),
            (1, 2): (1, 3), (2, 3): (1, 1), (3, 1): (1, 2),
            (2, 1): (-1, 3), (3, 2): (-1, 1), (1, 3): (-1, 2),
        }
        s, w = table[(u, v)]
        return s, w
    def mul_H(x, y):
        out = [0, 0, 0, 0]
        for u in range(4):
            for v in range(4):
                if x[u] and y[v]:
                    s, w = qmul(u, v)
                    out[w] += s * x[u] * y[v]
        return [c % p for c in out]
    circ = lambda x, y: [(a + b) % p for a, b in zip(mul_H(x, y), mul_H(y, x))]
    ok, dk, dz = determined(circ, 4, p)
    print(f"   H over F_3: zJpd = {ok} (dim ker = {dk}, dim Zs = {dz})")
    # sanity: it is a division algebra (no zero divisors)
    zero_div = any(not any(mul_H(list(x), list(y))) and any(x) and any(y)
                   for x in itertools.product(range(p), repeat=4)
                   for y in itertools.product(range(p), repeat=4))
    print(f"   has nonzero zero divisors: {zero_div} (True: the algebra is split over F_3)")


if __name__ == "__main__":
    main()
