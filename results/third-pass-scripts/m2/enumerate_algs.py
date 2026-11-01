"""Exhaustive enumeration of unital associative algebras of small dimension over F_p,
followed by a comparison of Der(A) with the space of local derivations."""
import itertools
import sys
import time
from linmod import span_basis, rank
from alg import Alg


def enumerate_algebras(p, n):
    """Yield Alg objects for all unital associative algebras with basis 1,e_1,...,e_{n-1}."""
    m = (n - 1) * (n - 1) * n   # number of free structure constants
    idx = lambda v: sum(c * p ** k for k, c in enumerate(v))
    for flat in range(p ** m):
        coords = []
        f = flat
        for _ in range(m):
            coords.append(f % p)
            f //= p
        # mult table as indices
        T = [[0] * n for _ in range(n)]
        unit = [1] + [0] * (n - 1)
        for i in range(n):
            for j in range(n):
                v = [0] * n
                if i == 0:
                    v[j] = 1
                elif j == 0:
                    v[i] = 1
                else:
                    k = ((i - 1) * (n - 1) + (j - 1)) * n
                    v = coords[k:k + n]
                T[i][j] = idx(v)
        # associativity
        ok = True
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if T[i][T[j][k]] != T[T[i][j]][k]:
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                break
        if not ok:
            continue
        mult = [[dec(v, p, n) for v in T[i]] for i in range(n)]
        yield Alg(p, mult, name="dim%d/F%d" % (n, p), one=0)


def dec(v, p, n):
    out = []
    for _ in range(n):
        out.append(v % p)
        v //= p
    return out


if __name__ == "__main__":
    p = int(sys.argv[1])
    n = int(sys.argv[2])
    t0 = time.time()
    total = 0
    zpd_alg = []
    for A in enumerate_algebras(p, n):
        total += 1
        dk, dz = A.zpd_data()
        if dk == dz:
            zpd_alg.append((A, dk))
    print("p=%d n=%d : %d associative unital, %d zpd [%.1fs]" % (p, n, total, len(zpd_alg), time.time() - t0))
    bad = 0
    for A, dk in zpd_alg:
        D = A.derivations()
        LD = A.local_derivations()
        if len(LD) > len(D):
            bad += 1
            print("  COUNTEREXAMPLE? dimDer=%d dimLDer=%d" % (len(D), len(LD)))
            print("  mult =", A.mult)
            for M in LD:
                isd, wit = A.is_derivation(M)
                if not isd:
                    print("   local non-derivation:", M, "fails at", wit)
                    break
    print("  zpd algebras with extra local derivations: %d [%.1fs]" % (bad, time.time() - t0))
