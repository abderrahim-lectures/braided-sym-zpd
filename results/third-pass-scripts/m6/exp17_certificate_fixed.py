"""Experiment 17 (fixed): certificate that A = K^3 is zpd but the twisted product
   mu_alpha(x,y) = xy + alpha(y)alpha(x),  alpha(e0)=e0, alpha(e1)=e2, alpha(e2)=e1+e2
   (unital, NOT multiplicative) is not determined, for each field where it fails.
The previous version of this script forgot the x_i*y_j coefficients; fixed here and
cross-checked against the dimension computation and against brute force.
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
                c = (x[i] * y[j]) % p
                for k in range(n):
                    out[k] = (out[k] + c * MU[i][j][k]) % p
        return tuple(out)

    el = list(product(range(p), repeat=n))
    # brute-force Z_mu and ker, and a certificate
    gens = []
    for x in el:
        for y in el:
            if not any(mu(x, y)):
                t = [0] * (n * n)
                for i in range(n):
                    if x[i]:
                        for j in range(n):
                            if y[j]:
                                t[i * n + j] = (x[i] * y[j]) % p
                gens.append(t)
    dimZ = rank(gens, p, n * n)
    U = mu_matrix(n, MU)
    dimker = n * n - rank(U, p, n * n)
    d = determined(n, MU, p)
    assert (dimZ, dimker) == d, (dimZ, dimker, d)
    # certificate: phi vanishing on all mu-zero pairs but not factoring through mu
    ann = kernel([[t[c] for c in range(n * n)] for t in gens], p, n * n)
    wit = None
    for phi in ann:
        seen = {}
        for x in el:
            for y in el:
                key = mu(x, y)
                val = sum(phi[i * n + j] * x[i] * y[j] for i in range(n) for j in range(n)) % p
                if key in seen and seen[key][1] != val:
                    wit = (phi, seen[key][0], seen[key][1], (x, y), val, key)
                    break
                seen[key] = ((x, y), val)
            if wit:
                break
        if wit:
            break
    print(f"p={p}: A=K^3 zpd={determined(n,A,p)[0]==determined(n,A,p)[1]}  "
          f"alpha unital={is_unital(n,A,ALPHA,p)} multiplicative={is_mult(n,A,ALPHA,p)}")
    print(f"      mu_alpha: dim Z={dimZ} dim ker={dimker} determined={dimZ==dimker}")
    if wit:
        phi, p1, v1, p2, v2, key = wit
        print(f"      certificate phi={phi}")
        print(f"        pair1 {p1}: mu={key} phi={v1} ;; pair2 {p2}: mu={key} phi={v2}  -> phi does not factor")
    else:
        print("      no certificate (consistent with determined)")


if __name__ == '__main__':
    for p in (2, 3, 5, 7, 11):
        run(p)
