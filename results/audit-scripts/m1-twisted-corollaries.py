#!/usr/bin/env python3
"""
m1 audit (swarm smvxd25ff) -- cor:twisted / cor:anti.

Question 1.  cor:twisted (paper line 321) says "Let A be commutative and zpd ..."
             with NO unital hypothesis, but its proof (line 326) applies
             Theorem thm:zpd-fxy, whose hypothesis (line 265) is "unital zpd" and
             whose proof uses the unit at line 274 (mu(b,1)=f(b)).
             Search all commutative algebras of small dimension over F_2 (and F_3)
             that are zpd but not unital, and test determination by
             mu_alpha(x,y) = xy + alpha(y)alpha(x) for every endomorphism alpha.

Question 2.  Associativity of the twisted product x*y = xy + alpha(y)alpha(x):
             exhibit a non-associative triple (the framework is non-associative,
             so this is only documented, not a defect).

Question 3.  "mu_alpha has no form f(xy)": check ker(m_bar) <= ker(mu_bar) for
             alpha = conjugation by diag(1,-1) on M_2(F_3) (linear-algebra form of
             "mu = f o product for some linear f").

Conventions: algebra of dimension n over F_p, T[i,j,k] = coefficient of e_k in e_i e_j.
"""
import itertools
import numpy as np

np.set_printoptions(linewidth=200)


def gauss(rows, ncols, p):
    """rank of the span of `rows` (list of int vectors of length ncols) over F_p"""
    basis = []          # list of (reduced vector, pivot column)
    for r in rows:
        v = np.asarray(r, dtype=np.int64).copy() % p
        for b, piv in basis:
            c = v[piv] % p
            if c:
                v = (v - c * b) % p
        nz = np.nonzero(v)[0]
        if nz.size:
            piv = int(nz[0])
            v = (v * pow(int(v[piv]), -1, p)) % p
            basis.append((v, piv))
    return len(basis)


def all_vecs(p, n):
    return np.array(list(itertools.product(range(p), repeat=n)), dtype=np.int64)


def mu_table(T, p, C=None):
    """T + alpha (x) alpha, where alpha has matrix C (alpha(e_i) = sum_l C[i,l] e_l)."""
    n = T.shape[0]
    if C is None:
        return T % p
    return (T + np.einsum('il,jm,lmk->ijk', C, C, T)) % p


def kerdim(Tm, p):
    """dim ker of the linear map A (x) A -> A, x (x) y |-> mu(x,y).
    Row k of the matrix must be the k-th coordinate of mu(e_i,e_j), i.e. the
    (k | i,j) layout -- NOT reshape(n,n*n), which would index (i | j,k)."""
    n = Tm.shape[0]
    M = np.transpose(Tm, (2, 0, 1)).reshape(n, n * n)
    return n * n - gauss([M[i] for i in range(n)], n * n, p)


def zsdim(Tm, p, vecs):
    """dim span{ x (x) y : mu(x,y)=0 }  over all x,y in A."""
    n = Tm.shape[0]
    P = np.einsum('ai,bj,ijk->abk', vecs, vecs, Tm) % p
    zero = (P == 0).all(axis=2)
    seen, rows = set(), []
    for a, b in zip(*np.nonzero(zero)):
        v = np.kron(vecs[a], vecs[b]) % p
        key = v.tobytes()
        if key not in seen:
            seen.add(key)
            rows.append(v)
    return gauss(rows, n * n, p), int(zero.sum())


def determined(Tm, p, vecs):
    return zsdim(Tm, p, vecs)[0] == kerdim(Tm, p)


def unital(T, p):
    n = T.shape[0]
    # look for u with u e_j = e_j for all j
    cand = all_vecs(p, n)
    for u in cand:
        ok = True
        for j in range(n):
            if not np.array_equal((np.einsum('i,ijk->jk', u, T) % p)[j], np.eye(n, dtype=np.int64)[j]):
                ok = False
                break
        if ok:
            return u
    return None


def endomorphisms(T, p):
    """all C with alpha(xy) = alpha(x)alpha(y)"""
    n = T.shape[0]
    out = []
    for code in range(p ** (n * n)):
        v = code
        C = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for l in range(n):
                C[i, l] = v % p
                v //= p
        lhs = np.einsum('il,jm,lmk->ijk', C, C, T) % p          # alpha(e_i)alpha(e_j)
        rhs = np.einsum('ijk,kl->ijl', T, C) % p                # alpha(e_i e_j)
        if np.array_equal(lhs, rhs):
            out.append(C)
    return out


def commutative_algebras(p, n):
    pairs = [(i, j) for i in range(n) for j in range(i, n)]
    block = p ** n
    total = block ** len(pairs)
    for code in range(total):
        c, T = code, np.zeros((n, n, n), dtype=np.int64)
        for (i, j) in pairs:
            w = c % block
            c //= block
            vec = np.zeros(n, dtype=np.int64)
            for k in range(n):
                vec[k] = w % p
                w //= p
            T[i, j] = vec
            T[j, i] = vec
        yield T


def scan(p, n, verbose=True, max_report=6):
    vecs = all_vecs(p, n)
    nzpd = nunital = 0
    findings = []
    for T in commutative_algebras(p, n):
        if not determined(mu_table(T, p), p, vecs):     # not zpd
            continue
        nzpd += 1
        if unital(T, p) is not None:
            continue
        nunital += 1
        for C in endomorphisms(T, p):
            Tm = mu_table(T, p, C)
            if not determined(Tm, p, vecs):
                findings.append((T.copy(), C.copy()))
                if len(findings) >= max_report:
                    break
        if len(findings) >= max_report:
            break
    if verbose:
        print(f"F_{p}, dim {n}: zpd commutative = {nzpd}, of them non-unital = {nunital}, "
              f"counterexamples to cor:twisted = {len(findings)}")
    return findings


def show(T, C, p):
    n = T.shape[0]
    print("  multiplication table (rows: e_i e_j, columns: coefficient of e_k):")
    for i in range(n):
        for j in range(i, n):
            print(f"    e{i}e{j} = " + " + ".join(f"{T[i,j,k]}e{k}" for k in range(n) if T[i, j, k]))
    print("  alpha matrix (columns = images of e_i):")
    print("   ", C.tolist())
    vecs = all_vecs(p, n)
    Tm = mu_table(T, p, C)
    print(f"    dim ker mu_bar = {kerdim(Tm,p)}, dim Zs_mu = {zsdim(Tm,p,vecs)[0]}, "
          f"dim Zs_product = {zsdim(T,p,vecs)[0]}, dim ker m_bar = {kerdim(T,p)}")
    print(f"    # zero mu pairs = {zsdim(Tm,p,vecs)[1]}, # zero product pairs = {zsdim(T,p,vecs)[1]}")


if __name__ == '__main__':
    for (p, n) in [(2, 2), (3, 2), (2, 3)]:
        fs = scan(p, n)
        for (T, C) in fs[:3]:
            print(f"--- counterexample over F_{p}, dim {n} ---")
            show(T, C, p)
