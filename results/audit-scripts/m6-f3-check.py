"""Independent check of the F_3 computations in prop:matrix of paper/braided-sym-zpd.tex.

M_2(F_3), alpha = conjugation by diag(1,-1). For a bilinear mu : A x A -> A we compute
  rank of mu-bar : A (x) A -> A     (16 x 16 matrix over F_3),
  dim ker mu-bar,
  the number of pairs (x,y) with mu(x,y) = 0 among the 81*81 pairs,
  the dimension of span{x (x) y : mu(x,y) = 0}.
Everything is done by brute force + exact Gaussian elimination over F_3.
"""
import itertools, sys

P = 3

def mat_vec(M):  # 2x2 matrix as tuple of 4 entries (row major)
    return tuple(M)

def mul(X, Y):
    return ((X[0]*Y[0]+X[1]*Y[2]) % P, (X[0]*Y[1]+X[1]*Y[3]) % P,
            (X[2]*Y[0]+X[3]*Y[2]) % P, (X[2]*Y[1]+X[3]*Y[3]) % P)

def add(X, Y): return tuple((a+b) % P for a, b in zip(X, Y))
def sc(c, X): return tuple((c*a) % P for a in X)
def trans(X): return (X[0], X[2], X[1], X[3])

ZERO = (0, 0, 0, 0)
BASIS = [(1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1)]

# conjugation by D = diag(1,-1):  D X D^{-1}
D = (1,0,0,2 % P)          # diag(1,-1) over F_3
Dinv = (1,0,0,2 % P)       # D^{-1} = D
def alpha(X): return mul(mul(D, X), Dinv)

def mu_twisted(X, Y):      # xy + alpha(y) alpha(x)  == xy + alpha(yx)
    return add(mul(X, Y), mul(alpha(Y), alpha(X)))

def mu_plain(X, Y): return mul(X, Y)

def mu_transpose(X, Y):    # xy + y^T x^T = xy + (xy)^T
    return add(mul(X, Y), trans(mul(X, Y)))

ALL = list(itertools.product(range(P), repeat=4))

def rank(rows, ncol):
    rows = [list(r) for r in rows if any(r)]
    r = 0
    for c in range(ncol):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] % P:
                piv = i; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], P-2, P)
        rows[r] = [(v*inv) % P for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f*b) % P for a, b in zip(rows[i], rows[r])]
        r += 1
    return r

def report(name, mu):
    # matrix of mu-bar in the tensor basis e_i (x) e_j (16 columns -> 4 coords)
    cols = []
    for i, ei in enumerate(BASIS):
        for j, ej in enumerate(BASIS):
            cols.append(mu(ei, ej))
    M = [[cols[c][r] for c in range(16)] for r in range(4)]
    rk = rank(M, 16)
    # zero pairs
    zt = []
    count = 0
    for X in ALL:
        for Y in ALL:
            if mu(X, Y) == ZERO:
                count += 1
                zt.append([(X[i]*Y[j]) % P for i in range(4) for j in range(4)])
    sdim = rank(zt, 16)
    print(f'{name:12s} rank(mu-bar) = {rk:2d}  dim ker = {16-rk:2d}  '
          f'#zero pairs = {count:5d}  dim span(zero tensors) = {sdim:2d}')
    return rk, count, sdim

print('field F_3, A = M_2(F_3), dim A = 4, dim A(x)A = 16')
r_t = report('twisted', mu_twisted)
r_p = report('plain', mu_plain)
r_s = report('transpose', mu_transpose)

# sanity: mu_twisted = xy + alpha(yx)
import random
random.seed(1)
for _ in range(200):
    X = tuple(random.randrange(P) for _ in range(4))
    Y = tuple(random.randrange(P) for _ in range(4))
    assert mu_twisted(X, Y) == add(mul(X, Y), alpha(mul(Y, X)))
print('identity mu(x,y) = xy + alpha(yx) verified on 200 random pairs')
print()
print('paper claims: twisted rank 4, dim ker 12, 417 zero pairs, span 12')
print('paper claims: plain "12 = 12", transpose "13 = 13"')
