"""Independent recomputation of every number in prop:matrix and the 13=13 remark
of paper/braided-sym-zpd.tex (v8).  Exact arithmetic over F_p, no floats.

Element of A = M_2(F_p): tuple (a,b,c,d) = a E11 + b E12 + c E21 + d E22.
Tensor x (x) y: tuple of length 16, index (i,j) -> x_i * y_j  (i = row-index of x, j of y).
"""
import itertools, sys
from fractions import Fraction

def matmul(x, y, p):
    # [[a,b],[c,d]] * [[e,f],[g,h]]
    a,b,c,d = x; e,f,g,h = y
    return ((a*e+b*g) % p, (a*f+b*h) % p, (c*e+d*g) % p, (c*f+d*h) % p)

def transpose(x): a,b,c,d = x; return (a,c,b,d)

def conj_diag(x):
    a,b,c,d = x; return (a, -b, -c, d)     # D X D^{-1}, D = diag(1,-1): flips off-diagonals

def echelon(rows, p):
    """Rank + a basis (list of tuples) of the span of `rows` over F_p."""
    basis = []
    for r in rows:
        r = [v % p for v in r]
        for (piv, br) in basis:
            if r[piv]:
                f = r[piv] * pow(br[piv], -1, p) % p
                r = [(rv - f*bv) % p for rv, bv in zip(r, br)]
        if any(r):
            piv = next(i for i, v in enumerate(r) if v)
            inv = pow(r[piv], -1, p)
            r = [v*inv % p for v in r]
            basis.append((piv, tuple(r)))
            basis.sort()
    return len(basis), basis

def span_dim(rows, p):
    return echelon(rows, p)[0]

def rank_and_kernel(mu, p):
    """mu: function (x,y) -> element of A.  Represented by the 4x16 matrix of mu_bar
    on basis tensors e_i (x) e_j.  Returns (rank, dim ker)."""
    basis_elts = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
    rows = []
    for i in range(4):
        for j in range(4):
            v = mu(basis_elts[i], basis_elts[j])
            rows.append([v[k] for k in range(4)])
    # rows are the images of the 16 basis tensors; rank of the 4x16 matrix = rank of rows
    r, _ = echelon(rows, p)
    return r, 16 - r

def zero_pairs_and_span(mu, p):
    """Enumerate x in A; for each x the set {y : mu(x,y)=0} is a subspace (mu linear in y);
    collect a spanning set of its tensors, plus the exact count of zero pairs."""
    elts = list(itertools.product(range(p), repeat=4))
    tensors = []
    count = 0
    # nullspace of y |-> mu(x,y) for each x: solve the 4x4 linear system
    for x in elts:
        # matrix M with columns mu(x, e_j)
        cols = [mu(x, e) for e in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]]
        # solve M y = 0 over F_p by brute force over the p^4 y's (p<=5: <=625)
        sols = [y for y in elts if mu(x, y) == (0,0,0,0)]
        count += len(sols)
        for y in sols:
            tensors.append(tuple(x[i]*y[j] % p for i in range(4) for j in range(4)))
    return count, span_dim(tensors, p)

def run(p):
    print(f"===== F_{p} =====")
    ordinary = lambda x, y: matmul(x, y, p)
    # braided products
    def mu_conj(x, y):                       # xy + alpha(y) alpha(x), alpha = conj by diag(1,-1)
        return tuple((u + v) % p for u, v in zip(matmul(x, y, p), matmul(conj_diag(y), conj_diag(x), p)))
    def mu_conj_yx(x, y):                    # xy + alpha(yx)  (equal to the above: alpha is an automorphism)
        return tuple((u + v) % p for u, v in zip(matmul(x, y, p), conj_diag(matmul(y, x, p))))
    def mu_T_braid(x, y):                    # braiding product with alpha = transpose: xy + y^T x^T = xy + (xy)^T
        xy = matmul(x, y, p)
        return tuple((u + v) % p for u, v in zip(xy, transpose(xy)))
    def mu_T_swap(x, y):                     # the *other* reading xy + alpha(yx) = xy + (yx)^T = xy + x^T y^T
        return tuple((u + v) % p for u, v in zip(matmul(x, y, p), transpose(matmul(y, x, p))))
    def mu_jordan(x, y):
        return tuple((u + v) % p for u, v in zip(matmul(x, y, p), matmul(y, x, p)))
    for name, mu in [("ordinary xy", ordinary),
                     ("twist conj(1,-1): xy+alpha(y)alpha(x)", mu_conj),
                     ("twist conj(1,-1): xy+alpha(yx)", mu_conj_yx),
                     ("Jordan xy+yx", mu_jordan),
                     ("transpose braiding xy + y^T x^T", mu_T_braid),
                     ("transpose 'xy + alpha(yx)' = xy + x^T y^T", mu_T_swap)]:
        r, dk = rank_and_kernel(mu, p)
        cnt, dz = zero_pairs_and_span(mu, p)
        verdict = "determined (Zs = ker)" if dz == dk else "NOT determined"
        print(f"  {name:42s} rank={r:2d} dim ker={dk:2d}  zero pairs={cnt:5d}  dim Zs={dz:2d}  {verdict}")

if __name__ == "__main__":
    for p in [3, 5, 2]:
        run(p)
