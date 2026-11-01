#!/usr/bin/env python3
"""m1: independent recomputation of the F_3 numerics in prop:matrix and the sentence after it,
plus the 'no form f(xy)' test.  (Cross-check for the report; prop:matrix numerics are d2's.)"""
import itertools, numpy as np
import importlib.util
spec = importlib.util.spec_from_file_location("ch", "results/audit-scripts/m1-twisted-checks.py")
ch = importlib.util.module_from_spec(spec); spec.loader.exec_module(ch)
p = 3
n = 2
T = ch.matrix_units(n, p)
vecs = ch.all_vecs(p, n * n)
print("dim A (x) A =", (n * n) ** 2)

def zero_pairs_count(Tm):
    P = np.einsum('ai,bj,ijk->abk', vecs, vecs, Tm) % p
    return int((P == 0).all(axis=2).sum())

def zs(Tm):
    return ch.zsdim(Tm, p, vecs)

# --- twisted product: alpha = conjugation by diag(1,-1)
C = ch.conj_matrix(n, p, np.array([1, -1]) % p)
Tm = ch.mu_table(T, p, C)
print("\n[twisted alpha = conj diag(1,-1)]")
print("  rank mu_bar =", ch.gauss([ch.mbar(Tm, p)[k] for k in range(4)], 16, p),
      "  dim ker mu_bar =", ch.kerdim(Tm, p))
print("  number of zero mu pairs =", zero_pairs_count(Tm), "  dim span of the zero tensors =", zs(Tm)[0])

# --- ordinary product
print("\n[ordinary product]")
print("  rank m_bar =", ch.gauss([ch.mbar(T, p)[k] for k in range(4)], 16, p),
      "  dim ker =", ch.kerdim(T, p), "  zero pairs =", zero_pairs_count(T),
      "  dim Zs =", zs(T)[0])

# --- twist by the transpose: mu(x,y) = xy + y^T x^T = xy + (xy)^T
Ct = np.zeros((4, 4), dtype=np.int64)
ix = lambda i, j: i * n + j
for i in range(n):
    for j in range(n):
        Ct[ix(i, j), ix(j, i)] = 1
TmT = ch.mu_table(T, p, Ct)
print("\n[twist by the transpose: mu(x,y) = xy + y^T x^T]")
print("  rank =", ch.gauss([ch.mbar(TmT, p)[k] for k in range(4)], 16, p),
      "  dim ker =", ch.kerdim(TmT, p), "  zero pairs =", zero_pairs_count(TmT),
      "  dim Zs =", zs(TmT)[0])
print("  (paper says: dim Zs = dim ker = 13)")

# --- sanity: does the transpose twist equal f(xy) with f = id + T?  yes: y^T x^T = (xy)^T
lf = np.einsum('iml,lk->imk', T, (np.eye(4, dtype=np.int64) + Ct) % p) % p
print("  mu_T = f(xy) with f = id + T ?", np.array_equal(TmT, lf))

# --- what a smaller presentation of the 417 number means: which pairs
print("\n[sanity] 81*81 =", 81 * 81)
