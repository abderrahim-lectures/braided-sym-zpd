"""m5: independent verification of the numerics of prop:matrix and of rem:inner.

Checks, over F_3, for A = M_2(F_3) (81 elements):
  * prop:matrix: #pairs with mu(x,y)=0 (claimed 417), rank of mu-bar (claimed 4),
    dim ker (claimed 12), span of the zero-product tensors (claimed 12);
  * the "12 = 12" for the ordinary product and the "13 = 13" for the transpose twist;
  * rem:inner: xy + alpha(yx) = (xD^{-1}) o (Dy) on every pair, and the intertwining
    relation bar-mu = bar-o after Phi;
  * rem:inner: e_ii + b e_ij is idempotent, and (e_ii + b e_ij) - e_ii = b e_ij is not.

Run:  python3 m5-f3.py
"""
p = 3


def mm(X, Y):
    return [[(X[0][0] * Y[0][0] + X[0][1] * Y[1][0]) % p,
             (X[0][0] * Y[0][1] + X[0][1] * Y[1][1]) % p],
            [(X[1][0] * Y[0][0] + X[1][1] * Y[1][0]) % p,
             (X[1][0] * Y[0][1] + X[1][1] * Y[1][1]) % p]]


def add(X, Y):
    return [[(X[i][j] + Y[i][j]) % p for j in range(2)] for i in range(2)]


def sub(X, Y):
    return [[(X[i][j] - Y[i][j]) % p for j in range(2)] for i in range(2)]


def tr(X):
    return [[X[j][i] for j in range(2)] for i in range(2)]


def idx(M):
    return ((M[0][0] * p + M[0][1]) * p + M[1][0]) * p + M[1][1]


ALLEL = [[[a, b], [c, d]] for a in range(p) for b in range(p)
         for c in range(p) for d in range(p)]
Z = [[0, 0], [0, 0]]
ONE = [[1, 0], [0, 1]]
D = [[1, 0], [0, p - 1]]
Dinv = [[1, 0], [0, p - 1]]  # D is its own inverse here


def alpha(X):
    return mm(mm(D, X), Dinv)


def mu_alpha(X, Y):
    return add(mm(X, Y), alpha(mm(Y, X)))


def mu_plain(X, Y):
    return mm(X, Y)


def mu_transp(X, Y):
    return add(mm(X, Y), mm(tr(Y), tr(X)))


def rank_over_Fp(rows, ncols):
    M = [list(r) for r in rows]
    rank = 0
    piv = 0
    while piv < ncols and rank < len(M):
        pivrow = None
        for i in range(rank, len(M)):
            if M[i][piv] % p:
                pivrow = i
                break
        if pivrow is None:
            piv += 1
            continue
        M[rank], M[pivrow] = M[pivrow], M[rank]
        inv = pow(M[rank][piv] % p, -1, p)
        M[rank] = [(v * inv) % p for v in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][piv] % p:
                f = M[i][piv] % p
                M[i] = [(M[i][k] - f * M[rank][k]) % p for k in range(ncols)]
        rank += 1
        piv += 1
    return rank


UNIT = {}
for i in range(2):
    for j in range(2):
        M = [[0, 0], [0, 0]]
        M[i][j] = 1
        UNIT[(i, j)] = M


def tensor_vec(X, Y):
    """X (x) Y in the basis E_ij (x) E_kl, index ((i*2+j)*2+k)*2+l."""
    v = [0] * 16
    for i in range(2):
        for j in range(2):
            for k in range(2):
                for l in range(2):
                    v[((i * 2 + j) * 2 + k) * 2 + l] = (X[i][j] * Y[k][l]) % p
    return v


def mu_matrix(mu):
    """16 x 16 matrix of the linearisation A (x) A -> A of mu."""
    Mat = [[0] * 16 for _ in range(p ** 4)]
    for c_el in range(16):
        l = c_el % 2
        k = (c_el // 2) % 2
        j = (c_el // 4) % 2
        i = (c_el // 8) % 2
        val = mu(UNIT[(i, j)], UNIT[(k, l)])
        for r in range(2):
            for c in range(2):
                Mat[idx(UNIT[(r, c)])][c_el] = val[r][c] % p
    return Mat


def analyse(mu, label):
    Mat = mu_matrix(mu)
    rk = rank_over_Fp([row for row in Mat], 16)
    zero_pairs = [(X, Y) for X in ALLEL for Y in ALLEL if mu(X, Y) == Z]
    tens = [tensor_vec(X, Y) for X, Y in zero_pairs]
    dimZs = rank_over_Fp(tens, 16) if tens else 0
    print(f"[{label}]  #zero pairs = {len(zero_pairs)} of 6561; "
          f"rank(mu-bar) = {rk}; dim ker = {16 - rk}; dim Zs = {dimZs}")
    return len(zero_pairs), rk, 16 - rk, dimZs


print("=== prop:matrix: alpha = conjugation by diag(1,-1) ===")
print("alpha involutive automorphism:",
      all(alpha(mu_plain(X, Y)) == mu_plain(alpha(X), alpha(Y)) for X in ALLEL for Y in ALLEL),
      "| alpha^2 = id:", all(alpha(alpha(X)) == X for X in ALLEL))
print("mu_alpha(x,y) = xy + alpha(y)alpha(x) for all pairs:",
      all(mu_alpha(X, Y) == add(mm(X, Y), mm(alpha(Y), alpha(X)))
          for X in ALLEL for Y in ALLEL))
analyse(mu_alpha, "prop:matrix   mu = xy + alpha(yx)")
analyse(mu_plain, "ordinary xy         ")
analyse(mu_transp, "transpose twist     ")
print("mu_transp(x,y) = xy + (xy)^T for all pairs:",
      all(mu_transp(X, Y) == add(mm(X, Y), tr(mm(X, Y))) for X in ALLEL for Y in ALLEL))

print("\n=== rem:inner ===")
bad = [(X, Y) for X in ALLEL for Y in ALLEL
       if mu_alpha(X, Y) != add(mm(mm(X, Dinv), mm(D, Y)), mm(mm(D, Y), mm(X, Dinv)))]
print("mismatches of xy + alpha(yx) = (xD^{-1}) o (Dy):", len(bad))

bad = []
for X in ALLEL:
    for Y in ALLEL:
        lhs = mu_alpha(X, Y)                      # bar-mu(x (x) y)
        Xp = mm(X, D)                             # Phi^{-1}(x (x) y) = xD (x) D^{-1} y
        Yp = mm(Dinv, Y)
        rhs = add(mm(Xp, Yp), mm(Yp, Xp))         # bar-o of the preimage
        if lhs != rhs:
            bad.append((X, Y))
print("mismatches of bar-mu = bar-o o Phi:", len(bad))
print("Phi maps a basis of A(x)A to a basis (rank of its matrix):",
      rank_over_Fp([tensor_vec(mm(UNIT[(i, j)], Dinv), mm(D, UNIT[(k, l)]))
                    for i in range(2) for j in range(2)
                    for k in range(2) for l in range(2)], 16))

print("\n=== the idempotents of rem:inner ===")
for i in range(2):
    for j in range(2):
        if i == j:
            continue
        ok = 0
        idem_of_diff = 0
        for b in ALLEL:
            E = [[b[r][c] if (r, c) == (i, j) else (1 if (r, c) == (i, i) else 0)
                  for c in range(2)] for r in range(2)]
            if mm(E, E) == E:
                ok += 1
            F = sub(E, UNIT[(i, i)])   # = b e_ij, "the difference of two idempotents"
            if mm(F, F) == F:
                idem_of_diff += 1
        print(f"  i={i} j={j}: e_ii + b e_ij idempotent for {ok}/81 b; "
              f"(e_ii+b e_ij)-e_ii = b e_ij idempotent for {idem_of_diff}/81 b")
