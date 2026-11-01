import numpy as np, itertools
import importlib.util
spec = importlib.util.spec_from_file_location("ch", "results/audit-scripts/m1-twisted-checks.py")
ch = importlib.util.module_from_spec(spec); spec.loader.exec_module(ch)

def conj_C(n, p, D):
    """matrix of alpha(x) = D x D^{-1} in the matrix-unit basis"""
    ix = lambda i, j: i * n + j
    C = np.zeros((n * n, n * n), dtype=np.int64)
    Dinv = np.linalg.inv(D.astype(float))
    assert np.allclose(Dinv, np.round(Dinv)), "D not invertible over the field"
    Dinv = np.round(Dinv).astype(np.int64) % p
    for i in range(n):
        for j in range(n):
            M = np.zeros((n, n), dtype=np.int64); M[i, j] = 1
            N = (D @ M @ Dinv) % p
            for a in range(n):
                for b in range(n):
                    C[ix(i, j), ix(a, b)] = N[a, b]
    return C

for (p, D, desc) in [
    (2, np.array([[1, 1], [0, 1]]), "F_2, D = [[1,1],[0,1]] (order 2, det 1)"),
    (2, np.array([[0, 1], [1, 1]]), "F_2, D = [[0,1],[1,1]] (order 3)"),
    (3, np.array([[1, 0], [0, 2]]), "F_3, D = diag(1,-1)  [prop:matrix]"),
    (2, np.array([[1, 0], [0, 1]]), "F_2, D = 1 (alpha = id: twisted = Jordan)"),
]:
    n = 2
    T = ch.matrix_units(n, p)
    C = conj_C(n, p, D)
    ok = np.array_equal(np.einsum('il,jm,lmk->ijk', C, C, T) % p, np.einsum('ijk,kl->ijl', T, C) % p)
    Tm = ch.mu_table(T, p, C)
    vecs = ch.all_vecs(p, n * n)
    D2 = (D @ D) % p
    print(f"{desc}: alpha multiplicative {ok}; alpha^2 = id? {np.array_equal(D2, np.eye(n,dtype=np.int64))}")
    print(f"   dim ker mu_bar = {ch.kerdim(Tm,p)}, dim Zs = {ch.zsdim(Tm,p,vecs)[0]} "
          f"-> determined: {ch.determined(Tm,p,vecs)}")
    # is mu of the form f(xy)?  ker m_bar <= ker mu_bar ?
    Mm, Mmu = ch.mbar(T, p), ch.mbar(Tm, p)
    r1 = ch.gauss([Mm[k] for k in range(n*n)], (n*n)**2, p)
    r2 = ch.gauss([Mm[k] for k in range(n*n)] + [Mmu[k] for k in range(n*n)], (n*n)**2, p)
    print(f"   rank m_bar = {r1}, rank [m_bar;mu_bar] = {r2} -> mu = f o product: {r1 == r2}")
