"""Correction of F4 (the "general transfer lemma" was FALSE as stated).

The judge's objection, which this script verifies independently:
"mu_bar onto" only makes every b a SUM of mu-products, and the proof needs b to be
a SINGLE mu-product.  Counterexample: the D1 algebra of the v7 swarm (associative,
non-unital, zpd, m_bar onto) with f(e0)=e0, f(e1)=0, f(e2)=e2: (A, f o m) is NOT
determined.  Also verified here: the correct sharp form is "every element is a
single mu-product", which a RIGHT identity supplies (no unit, no associativity
needed) -- matching lean/ZpdCore/Zpd.lean, theorem determined_comp_of_right_id.
"""
import itertools
from zpd_tools import Field, mu_matrix, mat_rank, kernel_dim

out = []


def say(*a):
    s = " ".join(str(x) for x in a)
    out.append(s)
    print(s)


def zero(F, n):
    return [F.zero] * n


def iszero(v):
    return all(c == 0 for c in v)


def mulv(F, mu, x, y, n):
    r = [F.zero] * n
    for k in range(n):
        s = F.zero
        for i in range(n):
            if x[i] == 0:
                continue
            for j in range(n):
                if y[j] == 0:
                    continue
                s = F.add(s, F.mul(x[i], F.mul(y[j], mu[i][j][k])))
        r[k] = s
    return r


def allv(F, n):
    return [list(v) for v in itertools.product(range(F.p), repeat=n)]


def dimZ(F, n, mu):
    V = allv(F, n)
    ts = []
    for x in V:
        for y in V:
            if iszero(mulv(F, mu, x, y, n)):
                ts.append([F.mul(x[i], y[j]) for i in range(n) for j in range(n)])
    return ts


def mu_mat(F, n, mu):
    return mu_matrix(F, n, mu)


def from_sc(F, sc):
    n = len(sc)
    return [[[F.elt(sc[i][j][k]) for k in range(n)] for j in range(n)] for i in range(n)]


def assoc(F, n, mu):
    for i in range(n):
        for j in range(n):
            for k in range(n):
                a = mulv(F, mu, mulv(F, mu, [F.one if t == i else F.zero for t in range(n)],
                                     [F.one if t == j else F.zero for t in range(n)], n),
                         [F.one if t == k else F.zero for t in range(n)], n)
                b = mulv(F, mu, [F.one if t == i else F.zero for t in range(n)],
                         mulv(F, mu, [F.one if t == j else F.zero for t in range(n)],
                              [F.one if t == k else F.zero for t in range(n)], n), n)
                if a != b:
                    return False
    return True


def units(F, n, mu):
    res = []
    for u in allv(F, n):
        ok = True
        for i in range(n):
            e = [F.one if t == i else F.zero for t in range(n)]
            if mulv(F, mu, u, e, n) != e or mulv(F, mu, e, u, n) != e:
                ok = False
                break
        if ok:
            res.append(u)
    return res


def single_products(F, n, mu, b):
    """is b a SINGLE mu-product?  exhaustive."""
    for x in allv(F, n):
        for y in allv(F, n):
            if mulv(F, mu, x, y, n) == b:
                return True
    return False


def determined(F, n, mu):
    Z = dimZ(F, n, mu)
    dz = mat_rank(F, Z)
    dk = kernel_dim(F, mu_mat(F, n, mu), n * n)
    return dz == dk, dz, dk, Z


def nullspace(F, rows, ncol):
    """basis of {v : rows . v = 0}."""
    R = [list(r) for r in rows]
    piv = []
    rank = 0
    for col in range(ncol):
        p = None
        for i in range(rank, len(R)):
            if not F.is_zero(R[i][col]):
                p = i
                break
        if p is None:
            continue
        R[rank], R[p] = R[p], R[rank]
        inv = F.div(F.one, R[rank][col])
        R[rank] = [F.mul(inv, x) for x in R[rank]]
        for i in range(len(R)):
            if i != rank and not F.is_zero(R[i][col]):
                fac = R[i][col]
                R[i] = [F.sub(R[i][k], F.mul(fac, R[rank][k])) for k in range(ncol)]
        piv.append(col)
        rank += 1
        if rank == len(R):
            break
    free = [c for c in range(ncol) if c not in piv]
    basis = []
    for fc in free:
        v = [F.zero] * ncol
        v[fc] = F.one
        for r, pc in enumerate(piv):
            v[pc] = F.sub(F.zero, R[r][fc])
        basis.append(v)
    return basis


def compose(F, n, f, mu):
    if F.p:
        return [[[sum(F.mul(f[k][l], mu[i][j][l]) for l in range(n)) % F.p
                  for k in range(n)] for j in range(n)] for i in range(n)]
    return [[[sum((F.mul(f[k][l], mu[i][j][l]) for l in range(n)), F.zero)
              for k in range(n)] for j in range(n)] for i in range(n)]


def certificate(F, n, mu, f):
    """nu := f o mu is not determined: exact certificate."""
    nu = compose(F, n, f, mu)
    Zn = dimZ(F, n, nu)
    dzn = mat_rank(F, Zn)
    dkn = kernel_dim(F, mu_mat(F, n, nu), n * n)
    say("    dim Z_nu = %d, dim ker nu_bar = %d, determined = %s"
        % (dzn, dkn, dzn == dkn))
    if dzn == dkn:
        return
    KN = nullspace(F, mu_mat(F, n, nu), n * n)
    T = None
    for t in KN:
        if mat_rank(F, Zn + [t]) > mat_rank(F, Zn):
            T = t
            break
    say("    T in ker nu_bar, T not in Z_nu:", T)
    ann = nullspace(F, Zn, n * n)   # l with l(z)=0 for every z in Z_nu
    l = None
    for v in ann:
        s = F.zero
        for a, b in zip(v, T):
            s = F.add(s, F.mul(a, b))
        if not F.is_zero(s):
            l = v
            break
    say("    l with l(Z_nu)=0 and l(T)!=0:", l)
    ok = True
    cnt = 0
    for x in allv(F, n):
        for y in allv(F, n):
            if iszero(mulv(F, nu, x, y, n)):
                cnt += 1
                s = F.zero
                for i in range(n):
                    for j in range(n):
                        s = F.add(s, F.mul(l[i * n + j], F.mul(x[i], y[j])))
                if not F.is_zero(s):
                    ok = False
    say("    phi(x,y)=l(x(x)y) vanishes on all %d nu-zero pairs: %s" % (cnt, ok))
    fibres = {}
    for x in allv(F, n):
        for y in allv(F, n):
            v = tuple(mulv(F, nu, x, y, n))
            s = F.zero
            for i in range(n):
                for j in range(n):
                    s = F.add(s, F.mul(l[i * n + j], F.mul(x[i], y[j])))
            fibres.setdefault(v, set()).add(s)
    say("    phi constant on the fibres of nu (= would factor through nu):",
        all(len(s) == 1 for s in fibres.values()))
    say("    moreover nu_bar(T)=0 while phi(T)=l(T)!=0, so no psi exists")


# ==================================================== (1) the D1 algebra
SC = [[[1, 0, 0], [0, 0, 1], [0, 0, 1]],
      [[0, 1, -1], [0, 0, 0], [0, 0, 0]],
      [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]
say("== (1) D1 algebra: e0e0=e0, e0e1=e2, e0e2=e2, e1e0=e1+e2, rest 0 ==")
for p in [2, 3, 5, 7]:
    F = Field(p)
    n = 3
    mu = from_sc(F, SC)
    say("  -- F_%d" % p)
    say("    associative:", assoc(F, n, mu), "  units:", units(F, n, mu))
    rk = mat_rank(F, mu_mat(F, n, mu))
    say("    rank(m_bar) = %d = dim A = %d -> m_bar ONTO: %s" % (rk, n, rk == n))
    det, dz, dk, Z = determined(F, n, mu)
    say("    zpd: dim Z_m = %d, dim ker m_bar = %d -> %s" % (dz, dk, det))
    bas = [[F.one if t == i else F.zero for t in range(n)] for i in range(n)]
    sp = [single_products(F, n, mu, b) for b in bas]
    say("    basis vectors that are a SINGLE product:", sp)
    f = [[F.one, F.zero, F.zero], [F.zero, F.zero, F.zero], [F.zero, F.zero, F.one]]
    mu_p = [[[sum(F.mul(f[k][l], mu[i][j][l]) for l in range(n)) % p
              for k in range(n)] for j in range(n)] for i in range(n)]
    detp, dzp, dkp, _ = determined(F, n, mu_p)
    say("    f=diag(1,0,1): (A, f o m) determined = %s  (dim Z=%d, dim ker=%d)"
        % (detp, dzp, dkp))
    if not detp:
        certificate(F, n, mu, f)

# ==================================================== (2) right-identity test
say("")
say("== (2) non-unital algebra WITH a right identity: mu(x,y)=(x1y1, x2y1) on K^2 ==")
for p in [2, 3, 5]:
    F = Field(p)
    n = 2
    mu = [[[F.zero] * n for _ in range(n)] for _ in range(n)]
    # e0*e0 = e0, e1*e0 = e1  (column matrices [[a,0],[b,0]])
    mu[0][0][0] = F.one
    mu[1][0][1] = F.one
    say("  -- F_%d" % p)
    say("    associative:", assoc(F, n, mu), "  two-sided units:", units(F, n, mu))
    e = [F.one, F.zero]
    say("    right identity e=(1,0): m(b,e)=b for all b:",
        all(mulv(F, mu, b, e, n) == b for b in allv(F, n)))
    det, dz, dk, Z = determined(F, n, mu)
    say("    zpd: dim Z=%d, dim ker=%d -> %s" % (dz, dk, det))
    say("    every basis vector a SINGLE product:",
        [single_products(F, n, mu, b) for b in [[F.one, F.zero], [F.zero, F.one]]])
    allok = True
    nf = 0
    for ent in itertools.product(range(p), repeat=4):
        f = [[F.elt(ent[0]), F.elt(ent[1])], [F.elt(ent[2]), F.elt(ent[3])]]
        mup = [[[sum(F.mul(f[k][l], mu[i][j][l]) for l in range(n)) % p
                 for k in range(n)] for j in range(n)] for i in range(n)]
        d, _, _, _ = determined(F, n, mup)
        nf += 1
        if not d:
            allok = False
    say("    (A, f o m) determined for all %d linear f: %s" % (nf, allok))

open("fix_f4.txt", "w").write("\n".join(out) + "\n")
