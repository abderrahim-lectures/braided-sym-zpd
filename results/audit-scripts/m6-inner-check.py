"""Check rem:inner numerically.

Claim (paper, rem:inner):  for alpha(x) = D x D^{-1} (D invertible),
    mu_alpha(x,y) = xy + alpha(yx) = xy + (Dy)(xD^{-1}) = (xD^{-1}) o (Dy),
so with Phi(x (x) y) = xD^{-1} (x) Dy (an automorphism of A(x)A carrying pure tensors to
pure tensors) mu-bar_alpha = o-bar o Phi, hence
    Z_{mu_alpha} = Phi^{-1}(Z_o)  and  ker mu-bar_alpha = Phi^{-1}(ker o-bar),
so determination by mu_alpha == determination by the Jordan product, independently of D.

We test on A = M_2(F_p) for p = 3, 5 and for two different invertible D (including a
non-diagonal one), for both the twisted product and the Jordan product:
  rank of mu-bar, dim ker, number of zero pairs, dimension of the span of the zero tensors.
"""
import itertools

def run(p, D):
    def mul(X, Y):
        return ((X[0]*Y[0]+X[1]*Y[2]) % p, (X[0]*Y[1]+X[1]*Y[3]) % p,
                (X[2]*Y[0]+X[3]*Y[2]) % p, (X[2]*Y[1]+X[3]*Y[3]) % p)
    def add(X, Y): return tuple((a+b) % p for a, b in zip(X, Y))
    def det(X): return (X[0]*X[3]-X[1]*X[2]) % p
    assert det(D) % p, 'D not invertible'
    Dinv = (D[3]*pow(det(D), p-2, p) % p, (-D[1])*pow(det(D), p-2, p) % p,
            (-D[2])*pow(det(D), p-2, p) % p, D[0]*pow(det(D), p-2, p) % p)
    def alpha(X): return mul(mul(D, X), Dinv)
    def mu(X, Y): return add(mul(X, Y), alpha(mul(Y, X)))
    def jor(X, Y): return add(mul(X, Y), mul(Y, X))
    BAS = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
    ALL = list(itertools.product(range(p), repeat=4))
    def rank(rows, n=16):
        rows = [[v % p for v in r] for r in rows if any(r)]
        r = 0
        for c in range(n):
            piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], p-2, p)
            rows[r] = [(v*inv) % p for v in rows[r]]
            for i in range(len(rows)):
                if i != r and rows[i][c]:
                    f = rows[i][c]
                    rows[i] = [(a-f*b) % p for a, b in zip(rows[i], rows[r])]
            r += 1
        return r
    def stats(f):
        cols = [f(ei, ej) for ei in BAS for ej in BAS]
        rk = rank([[cols[c][i] for c in range(16)] for i in range(4)])
        zt, cnt = [], 0
        for X in ALL:
            for Y in ALL:
                if f(X, Y) == (0,0,0,0):
                    cnt += 1
                    zt.append([X[i]*Y[j] % p for i in range(4) for j in range(4)])
        return rk, 16-rk, cnt, rank(zt)
    return stats(mu), stats(jor)

for p in (3, 5):
    for D in [(1,0,0,p-1), (1,1,0,1), (1,2,1,0)]:
        if D == (1,2,1,0) and p == 3:   # det = -2 = 1 mod 3, fine; keep all
            pass
        t, j = run(p, D)
        print(f'p={p} D={D}: twisted rank/ker/#zero/span = {t},  jordan = {j},  '
              f'identical shapes: {t[0]==j[0] and t[1]==j[1] and t[2]==j[2] and t[3]==j[3]}')
print()
print('(e_ii + b e_ij) - e_ii == b e_ij is nilpotent, hence not an idempotent:')
print('  (b e_ij)^2 = b e_ij b e_ij = b (e_ij e_ij) b = 0  because e_ij e_ij = 0 for i != j')
