"""Experiment 13 (p=2, fast path): M_2(B) for non-zpd B, and other larger zpd algebras --
looking for a unital zpd algebra that is not zJpd.
"""
import sys
sys.path.insert(0, '.')
from zpd import *
from fast2 import determined2
from exp11_matrix_over_B import mat_alg, Kx3
from exp7_families import ladder
from exp5_structured import table_from_units, direct_sum


def check(name, T):
    n = len(T)
    dm = determined2(n, T)
    dj = determined2(n, jordan_mu_p(n, T, 2))
    print(f"F_2 {name}: dim={n} product {dm} zpd={dm[0]==dm[1]}   Jordan {dj} zJpd={dj[0]==dj[1]}",
          flush=True)


if __name__ == '__main__':
    # sanity check of fast path against the slow one
    T2 = alg_upper_triangular(2, 2)
    print("sanity M_2(F_2):", determined(4, alg_matrix_units(2, 2), 2), determined2(4, alg_matrix_units(2, 2)))
    for Bname, B in (("ladder", ladder(2)), ("K[x]/x^3", Kx3(2)), ("dual", alg_dual_numbers(2))):
        A = mat_alg(2, B, 2)
        check(f"M_2({Bname})", A)
    check("M_3(F_2)", alg_matrix_units(3, 2))
    check("T_4(F_2)", alg_upper_triangular(4, 2))
    check("Tri(K,K^2,K^2,K) (5)", None) if False else None
