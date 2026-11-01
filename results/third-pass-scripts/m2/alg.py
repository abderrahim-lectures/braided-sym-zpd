"""Derivations, local derivations, zpd test for finite-dimensional F_p-algebras."""
import itertools
from linmod import rref, nullspace, span_basis, rank, annihilator


class Alg:
    """Finite-dimensional F_p-algebra given by structure constants.

    mult[i][j] is the coefficient vector of e_i e_j in the basis (e_0,...,e_{n-1}).
    """

    def __init__(self, p, mult, name="", one=0):
        self.p = p
        self.mult = [[tuple(x % p for x in row) for row in mrow] for mrow in mult]
        self.n = len(mult)
        self.name = name
        self.one = one

    def prod(self, x, y):
        p, n = self.p, self.n
        out = [0] * n
        for i in range(n):
            if x[i]:
                xi = x[i]
                for j in range(n):
                    if y[j]:
                        f = xi * y[j] % p
                        m = self.mult[i][j]
                        for k in range(n):
                            if m[k]:
                                out[k] = (out[k] + f * m[k]) % p
        return tuple(out)

    def is_associative(self):
        p, n = self.p, self.n
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if self.prod(self.mult[i][j], self.unit(k)) != self.prod(
                            self.unit(i), self.mult[j][k]):
                        return False
        return True

    def unit(self, k):
        v = [0] * self.n
        v[k] = 1
        return tuple(v)

    def one_vec(self):
        return self.unit(self.one)

    def is_unital(self):
        e = self.one_vec()
        return all(self.prod(e, self.unit(i)) == self.unit(i) and
                   self.prod(self.unit(i), e) == self.unit(i) for i in range(self.n))

    def elements(self):
        for v in itertools.product(range(self.p), repeat=self.n):
            yield v

    # ---------- zpd ----------
    def zpd_data(self):
        """Return (dim ker mubar, dim Z_mu) for mu = the product.

        Z_mu = span{x (x) y : xy = 0}.  Its dimension is computed as n^2 minus
        the dimension of its annihilator in the space of bilinear forms:
        B vanishes on every zero-product tensor iff for every x, B(x, .) vanishes
        on ker(y |-> xy).
        """
        p, n = self.p, self.n
        # mubar : A (x) A -> A, columns indexed by (i,j)
        rows = []
        for l in range(n):
            row = []
            for i in range(n):
                for j in range(n):
                    row.append(self.mult[i][j][l])
            rows.append(row)
        dimker = len(nullspace(rows, p, n * n))
        # annihilator of Z_mu inside the space of bilinear forms (n x n entries)
        brows = []
        for x in self.elements():
            if not any(x):
                continue
            # matrix of y |-> x*y
            mrows = []
            for l in range(n):
                mrows.append([sum(x[i] * self.mult[i][j][l] for i in range(n)) % p
                              for j in range(n)])
            for y in nullspace(mrows, p, n):
                brows.append([x[i] * y[j] % p for i in range(n) for j in range(n)])
        # The rows just built ARE the zero-product tensors x (x) y, so their
        # rank is dim Z_mu directly.
        dimZ = rank(brows, p, n * n)
        return dimker, dimZ

    def is_zpd(self):
        a, b = self.zpd_data()
        return a == b

    # ---------- derivations ----------
    def derivations(self):
        """Basis of Der(A) as list of n x n matrices (mat[j][k]: coeff of e_k in D(e_j))."""
        p, n = self.p, self.n
        nunk = n * n
        # residual coefficient vectors for each unit unknown
        resid = []  # list over unknowns of dict (i,j)->vector
        for j0 in range(n):
            for k0 in range(n):
                # D(e_j) = delta_{j,j0} e_{k0}
                def D(v):
                    out = [0] * n
                    c = v[j0]
                    if c:
                        out[k0] = c % p
                    return out
                block = []
                for i in range(n):
                    for j in range(n):
                        # D(e_i e_j) - D(e_i)e_j - e_i D(e_j)
                        r = list(D(self.mult[i][j]))
                        t = self.prod(D(self.unit(i)), self.unit(j))
                        for k in range(n):
                            r[k] = (r[k] - t[k]) % p
                        t = self.prod(self.unit(i), D(self.unit(j)))
                        for k in range(n):
                            r[k] = (r[k] - t[k]) % p
                        block.append(r)
                resid.append(block)
        rows = []
        for m in range(n * n):
            for l in range(n):
                rows.append([resid[u][m][l] for u in range(nunk)])
        sols = nullspace(rows, p, nunk)
        out = []
        for s in sols:
            mat = [[s[j * n + k] for k in range(n)] for j in range(n)]
            out.append(mat)
        return out

    def apply(self, mat, a):
        p, n = self.p, self.n
        out = [0] * n
        for j in range(n):
            aj = a[j]
            if aj:
                for k in range(n):
                    if mat[j][k]:
                        out[k] = (out[k] + aj * mat[j][k]) % p
        return tuple(out)

    def local_derivations(self):
        """Basis of the space of local derivations.

        D is local iff for every a in A there is a derivation Delta with D(a)=Delta(a).
        This is a linear condition on D, so the set is a subspace.
        """
        p, n = self.p, self.n
        D = self.derivations()
        nunk = n * n
        rows = []
        for a in self.elements():
            if not any(a):
                continue
            imgs = [self.apply(d, a) for d in D]  # V_a
            ann = annihilator(imgs, p, n)
            for lam in ann:
                row = [0] * nunk
                for i in range(n):
                    if a[i]:
                        for k in range(n):
                            row[i * n + k] = (row[i * n + k] + a[i] * lam[k]) % p
                rows.append(row)
        sols = nullspace(rows, p, nunk) if rows else [[1 if j == k else 0 for k in range(nunk)]
                                                     for j in range(nunk)]
        out = []
        for s in sols:
            out.append([[s[j * n + k] for k in range(n)] for j in range(n)])
        return out

    def is_derivation(self, mat):
        p, n = self.p, self.n
        for i in range(n):
            for j in range(n):
                lhs = self.apply(mat, self.mult[i][j])
                rhs = self.prod(self.apply(mat, self.unit(i)), self.unit(j))
                rhs2 = self.prod(self.unit(i), self.apply(mat, self.unit(j)))
                rhs = tuple((rhs[k] + rhs2[k]) % p for k in range(n))
                if lhs != rhs:
                    return False, (i, j)
        return True, None

    def check_local(self, mat):
        """Verify directly (by exhaustive check over A) that mat is a local derivation:
        D(a) must lie in the SPAN of {Delta(a) : Delta a derivation}."""
        from linmod import rank
        D = self.derivations()
        bad = []
        for a in self.elements():
            img = self.apply(mat, a)
            if not any(img):
                continue
            imgs = [list(self.apply(d, a)) for d in D]
            if rank(imgs + [list(img)], self.p, self.n) > rank(imgs, self.p, self.n):
                bad.append((a, img))
        return bad

    # ---------- idempotents ----------
    def idempotents(self):
        return [a for a in self.elements() if self.prod(a, a) == a]

    def generated_dim(self, gens):
        """Dimension of the subalgebra generated by gens (must contain the unit or not)."""
        p, n = self.p, self.n
        basis = []
        frontier = [tuple(g) for g in gens]
        seen = set()
        allvecs = []
        # BFS over products of basis elements
        cur = span_basis([list(v) for v in frontier] + ([list(self.one_vec())] if self.one is not None else []), p, n)
        while True:
            newv = list(cur)
            for x in cur:
                for y in cur:
                    pr = list(self.prod(x, y))
                    if rank(newv + [pr], p, n) > rank(newv, p, n):
                        newv.append(pr)
            if rank(newv, p, n) == rank(cur, p, n):
                return rank(cur, p, n)
            cur = span_basis(newv, p, n)
