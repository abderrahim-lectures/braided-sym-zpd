from build import express
from alg import Alg
from linmod import rank

def flat(M): return [x for row in M for x in row]
def unflat(v, s): return [v[i*s:(i+1)*s] for i in range(s)]

def alg_from_spanning(p, mats, name=""):
    s = len(mats[0])
    basis = []
    coords_of = []
    for M in mats:
        v = [x % p for x in flat(M)]
        if rank(basis + [v], p, s*s) > len(basis):
            basis.append(v); coords_of.append(express(p, [unflat(b, s) for b in basis], M))
        else:
            coords_of.append(None)
    n = len(basis)
    bm = [unflat(v, s) for v in basis]
    mult = []
    for i in range(n):
        row = []
        for j in range(n):
            prod = [[sum(bm[i][a][b]*bm[j][b][c] for b in range(s)) % p for c in range(s)] for a in range(s)]
            row.append(express(p, bm, prod))
        mult.append(row)
    A = Alg(p, mult, name=name, one=None)
    ident = [[1 if a == b else 0 for b in range(s)] for a in range(s)]
    try:
        A.unit_coords = express(p, bm, ident)
    except ValueError:
        A.unit_coords = None
    return A

def reduce_span(p, mats):
    s = len(mats[0]); basis=[]
    for M in mats:
        v=[x % p for x in flat(M)]
        if rank(basis+[v], p, s*s) > len(basis): basis.append(v)
    return [unflat(v,s) for v in basis]

def M(p, m, name=""):
    mats=[]
    for a in range(m):
        for b in range(m):
            E=[[0]*m for _ in range(m)]; E[a][b]=1; mats.append(E)
    return alg_from_spanning(p, mats, name or "M_%d(F_%d)"%(m,p))

def T(p, m, name=""):
    mats=[]
    for a in range(m):
        for b in range(a,m):
            E=[[0]*m for _ in range(m)]; E[a][b]=1; mats.append(E)
    return alg_from_spanning(p, mats, name or "T_%d(F_%d)"%(m,p))

def prod_of(A1, A2, p, name):
    """direct product B x C as block diagonal matrices."""
    s1 = None
    # matrices from the spanning data are not stored; rebuild from the abstract tables instead
    raise NotImplementedError
