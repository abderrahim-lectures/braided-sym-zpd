"""Experiment 18: Tri(A_1, M, A_2) with A_1 = M_2 (noncommutative), M = K^2 the natural module,
A_2 = K.  zpd by Bresar Cor 2.17(b).  Test [A,A] <= W and zJpd.
Feeds the reduction proved in report.md D8-3.
"""
import sys
from itertools import product
sys.path.insert(0, '.')
from zpd import *
from exp8_commutator_in_W import W_and_commutators, contains


def tri_M2_K2_K(p):
    """elements (X,m,c): X in M_2 (basis E11,E12,E21,E22), m in K^2 (basis f1,f2), c in K.
    product: (X,m,c)(X',m',c') = (X X', X m' + m c', c c')."""
    n = 4 + 2 + 1
    T = [[[0] * n for _ in range(n)] for _ in range(n)]
    def iX(a, b):        # E_ab, a,b in {1,2}
        return (a - 1) * 2 + (b - 1)
    fm = 4
    fc = 6
    # A_1 part
    for a in (1, 2):
        for b in (1, 2):
            for c in (1, 2):
                T[iX(a, b)][iX(b, c)][iX(a, c)] = (T[iX(a, b)][iX(b, c)][iX(a, c)] + 1) % p
    # X * m'  : E_ab acts on f_j = delta_{b? } -- M = K^2 as left M_2 module: E_ab f_j = delta_{b j} f_a
    for a in (1, 2):
        for b in (1, 2):
            for j in (1, 2):
                if b == j:
                    T[iX(a, b)][fm + j - 1][fm + a - 1] = (T[iX(a, b)][fm + j - 1][fm + a - 1] + 1) % p
    # m * c' : f_j * c = c f_j
    for j in (1, 2):
        T[fm + j - 1][fc][fm + j - 1] = (T[fm + j - 1][fc][fm + j - 1] + 1) % p
    # A_2 part
    T[fc][fc][fc] = 1 % p
    return T


def report(name, T, p):
    n = len(T)
    assert is_associative(n, T, p), f"{name} not associative"
    dm = determined(n, T, p)
    dj = determined(n, jordan_mu_p(n, T, p), p)
    dimW, dimC, W, C = W_and_commutators(n, T, p)
    print(f"p={p} {name}: n={n} product {dm} zpd={dm[0]==dm[1]}; Jordan {dj} zJpd={dj[0]==dj[1]}; "
          f"dimW={dimW} dim[A,A]={dimC} [A,A]<=W={contains(W, C, p, n)}", flush=True)


if __name__ == '__main__':
    for p in (2, 3):
        report("Tri(M_2,K^2,K)", tri_M2_K2_K(p), p)
