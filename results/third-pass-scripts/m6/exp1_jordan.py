"""First experiment: for unital algebras, compare
   zpd        = determined by the product m
   zJpd       = determined by the Jordan product x*y + y*x .
Question (swarm-new):  does zpd of a unital algebra imply zJpd?
"""
import sys
sys.path.insert(0, '.')
from zpd import *


def report(name, n, T, p):
    d_m = determined(n, T, p)
    d_j = determined(n, jordan_mu_p(n, T, p), p)
    zpd = d_m[0] == d_m[1]
    zjpd = d_j[0] == d_j[1]
    print(f"p={p}  {name:28s} dimZ_m/dimker_m={d_m}  zpd={zpd}   "
          f"dimZ_J/dimker_J={d_j}  zJpd={zjpd}")
    return (d_m, d_j)


if __name__ == '__main__':
    for p in (2, 3):
        report("F_p^2", 2, alg_diagonal(2, p), p)
        report("F_p^3", 3, alg_diagonal(3, p), p)
        report("T_2", 3, alg_upper_triangular(2, p), p)
        report(f"M_2(F_{p})", 4, alg_matrix_units(2, p), p)
        report("dual numbers", 2, alg_dual_numbers(p), p)
        if p == 2:
            report("T_3", 6, alg_upper_triangular(3, p), p)
            report("M_3", 9, alg_matrix_units(3, p), p)
