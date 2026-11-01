#!/usr/bin/env python3
"""Independent check of paper/braided-sym-zpd.tex, Proposition prop:matrix (Lemma about M_2(F_3))
and of the two 'dim Z = dim ker' sentences that follow it, plus the Introduction's K x K
parenthetical and the 'no form f(xy)' claim for the inner twist.

Everything is done over F_3 with exact mod-3 arithmetic; no external dependency.
"""
from itertools import product

P = 3
def inv(a): return pow(a % P, P - 2, P)

# ---------- M_2(F_3): elements are tuples (a,b,c,d) = [[a,b],[c,d]] ----------
def add(x, y): return tuple((x[i] + y[i]) % P for i in range(4))
def sub(x, y): return tuple((x[i] - y[i]) % P for i in range(4))
def mul(x, y):
    a,b,c,d = x; e,f,g,h = y
    return ((a*e + b*g) % P, (a*f + b*h) % P, (c*e + d*g) % P, (c*f + d*h) % P)
def scal(k, x): return tuple((k*t) % P for t in x)
ZERO = (0,0,0,0); ONE = (1,0,0,1)
BASIS = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
def mat(entries): return tuple(t % P for t in entries)
def tr(x): return (x[0], x[2], x[1], x[3])
def alpha(x):                       # conjugation by diag(1,-1) = (1,-1) = (1,2) in F_3
    return (x[0], (-x[1]) % P, (-x[2]) % P, x[3])
def check_alpha_involutive_automorphism():
    assert all(alpha(alpha(x)) == x for x in allmat())
    assert all(alpha(mul(x,y)) == mul(alpha(x), alpha(y)) for x in allmat() for y in allmat())
def allmat(): return [mat(t) for t in product(range(P), repeat=4)]

# ---------- the three products ----------
def mu_alpha(x, y):  return add(mul(x, y), alpha(mul(y, x)))       # xy + alpha(yx)
def mu_ord(x, y):    return mul(x, y)                              # xy
def mu_tr(x, y):     return add(mul(x, y), tr(mul(x, y)))          # xy + (xy)^T

def as_vec(x): return x                                            # 4 coordinates

def tensor(i, j):   # e_i (x) e_j as a 16-vector, index i*4+j
    v = [0]*16; v[4*i+j] = 1; return tuple(v)

def mu_bar_matrix(mu):
    """4 x 16 matrix of the linear map mu-bar : A (x) A -> A on the basis e_i (x) e_j."""
    rows = []
    for r in range(4):
        row = []
        for i in range(4):
            for j in range(4):
                row.append(mu(BASIS[i], BASIS[j])[r] % P)
        rows.append(row)
    return rows

def rref(rows, ncols):
    """Gauss-Jordan over F_p; returns (rref rows, pivot columns)."""
    M = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(M)):
            if M[i][c] % P:
                p = i; break
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        k = inv(M[r][c])
        M[r] = [(k*t) % P for t in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % P:
                f = M[i][c]
                M[i] = [(M[i][j] - f*M[r][j]) % P for j in range(ncols)]
        piv.append(c); r += 1
        if r == len(M): break
    return M[:r], piv

def rank(rows, ncols): return len(rref(rows, ncols)[1])

def kernel_basis(rows, ncols):
    R, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [0]*ncols; v[f] = 1
        for i, c in enumerate(piv):
            v[c] = (-R[i][f]) % P
        basis.append(tuple(v))
    return basis

def in_span(v, basis):
    """is the 16-vector v in the span of basis (over F_p)?"""
    if not basis: return all(t % P == 0 for t in v)
    r = rank([list(b) for b in basis] + [list(v)], len(v))
    return r == rank([list(b) for b in basis], len(v))

def analyse(name, mu):
    Mb = mu_bar_matrix(mu)
    rk = rank(Mb, 16)
    kb = kernel_basis(Mb, 16)
    zeros = []
    allx = allmat()
    for x in allx:
        for y in allx:
            if all(t % P == 0 for t in mu(x, y)):
                # x (x) y as a 16-vector
                v = [0]*16
                for i in range(4):
                    if x[i] % P == 0: continue
                    for j in range(4):
                        if y[j] % P == 0: continue
                        v[4*i+j] = (v[4*i+j] + x[i]*y[j]) % P
                zeros.append(tuple(v))
    span = rank([list(v) for v in zeros], 16)
    # every generating tensor must lie in ker mu-bar (this is what makes Z_mu <= ker mu-bar)
    allin = all(in_span(v, kb) for v in zeros)
    print(f"{name}: rank(mu-bar) = {rk}, dim ker = {16-rk}, "
          f"#{{(x,y): mu(x,y)=0}} = {len(zeros)}, dim span{{x(x)y}} = {span}, "
          f"span <= ker: {allin}, Z_mu == ker: {span == 16-rk and allin}")
    return dict(rank=rk, ker=16-rk, zeros=len(zeros), span=span, allin=allin, kb=kb)

print("alpha involutive automorphism:", end=" ")
check_alpha_involutive_automorphism(); print("yes")
A = analyse("twisted alpha = conj by diag(1,-1)", mu_alpha)
B = analyse("ordinary product xy               ", mu_ord)
C = analyse("transpose twist xy + (xy)^T       ", mu_tr)

# ---- is mu_alpha of the form f(xy)?  i.e. does it factor through the product? ----
Mb = mu_bar_matrix(mu_ord)
ker_m = kernel_basis(Mb, 16)
Ma = mu_bar_matrix(mu_alpha)
ker_a = kernel_basis(Ma, 16)
print("\nker m <= ker mu_alpha (necessary for mu_alpha = f(xy)):",
      all(in_span(v, ker_a) for v in ker_m))
def pair_witnesses(mu):
    vals, wits = {}, []
    for x in allmat():
        for y in allmat():
            p = mul(x, y); v = mu(x, y)
            if p in vals:
                if vals[p] != v: wits.append((p, vals[p], (x, y), v))
            else:
                vals[p] = v
    return wits
wa = pair_witnesses(mu_alpha); wt = pair_witnesses(mu_tr)
print("pairs (x,y),(x',y') with xy = x'y' but mu_alpha(x,y) != mu_alpha(x',y'):", len(wa))
print("  first witness (product, mu, second pair, its mu):", wa[0])
print("same count for the transpose twist xy + (xy)^T:", len(wt), "(0 = it is a function of xy)")

# ---- Introduction parenthetical: K x K, alpha(x,y) = (x+y,0), pairs (e1,e1) and (e1,1) ----
# work over Q so that 2 != 3 is visible
def kk_mul(x, y): return (x[0]*y[0], x[1]*y[1])
def kk_alpha(x): return (x[0] + x[1], 0)
e1, one = (1, 0), (1, 1)
def kk_mu(x, y):
    p = kk_mul(x, y); q = kk_mul(kk_alpha(y), kk_alpha(x))
    return (p[0] + q[0], p[1] + q[1])
print("\nK x K parenthetical: product (e1,e1) =", kk_mul(e1, e1), " (e1,1) =", kk_mul(e1, one))
print("                     mu(e1,e1) =", kk_mu(e1, e1), " mu(e1,1) =", kk_mu(e1, one))
print("alpha multiplicative?", all(kk_alpha(kk_mul(x, y)) == kk_mul(kk_alpha(x), kk_alpha(y))
                                for x in [(0,1),(1,0),(1,1),(2,3)] for y in [(0,1),(1,0),(1,1),(2,3)]))
