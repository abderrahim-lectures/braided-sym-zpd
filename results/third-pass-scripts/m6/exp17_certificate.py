"""Experiment 17: certificate, for each field, that A = K^3 is zpd but the twisted product
   mu_alpha(x,y) = xy + alpha(y)alpha(x),  alpha(e0)=e0, alpha(e1)=e2, alpha(e2)=e1+e2
   (unital, NOT multiplicative) is not determined.
Certificate: phi(x,y) = x_0 y_0 vanishes on every mu-zero pair, but two pairs have the same
mu and different phi.
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *
from exp16_twisted_alpha import mu_twisted, is_mult, is_unital

ALPHA = [[1, 0, 0], [0, 0, 1], [0, 1, 1]]


def run(p):
    n = 3
    A = alg_diagonal(n, p)
    MU = mu_twisted(n, A, ALPHA, p)
    def mu(x, y):
        out = [0] * n
        for i in range(n):
            if not x[i]:
                continue
            for j in range(n):
                if not y[j]:
                    continue
                for k in range(n):
                    out[k] = (out[k] + MU[i][j][k]) % p
        return tuple(out)
    phi = [1, 0, 0, 0, 0, 0, 0, 0, 0]          # phi(x,y) = x_0 y_0
    def phival(x, y):
        return sum(phi[i * n + j] * x[i] * y[j] for i in range(n) for j in range(n)) % p
    el = list(product(range(p), repeat=n))
    zeropair_ok = all(phival(x, y) == 0 for x in el for y in el if not any(mu(x, y)))
    d = determined(n, MU, p)
    dm = determined(n, A, p)
    # find witness pairs with equal mu, different phi
    seen = {}
    wit = None
    for x in el:
        for y in el:
            key = mu(x, y)
            val = phival(x, y)
            if key in seen and seen[key][1] != val:
                wit = (seen[key][0], seen[key][1], (x, y), val, key)
                break
            seen[key] = ((x, y), val)
        if wit:
            break
    print(f"p={p}: A=K^3 zpd={dm[0]==dm[1]} {dm};  alpha unital={is_unital(n,A,ALPHA,p)} "
          f"multiplicative={is_mult(n,A,ALPHA,p)}")
    print(f"      mu_alpha: dim Z={d[0]} dim ker={d[1]} determined={d[0]==d[1]}")
    print(f"      phi(x,y)=x0*y0 vanishes on every mu-zero pair: {zeropair_ok}")
    print(f"      witness: {wit[0]} and {wit[2]} have mu = {wit[4]}, phi = {wit[1]} resp. {wit[3]}")


if __name__ == '__main__':
    for p in (2, 3, 5, 7, 11):
        run(p)
