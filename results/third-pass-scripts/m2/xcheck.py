"""Independent derivation computation via sympy/symbolic solve, M_2(F_p)."""
import sympy as sp

def der_dim(p, m=2):
    # basis: I, then E_ij row-major; algebra structure constants
    N = m*m+1
    basis = {}
    idx = {}
    idx[None] = 0
    k=1
    for i in range(m):
        for j in range(m):
            idx[(i,j)]=k; k+=1
    # matrices
    mats=[]
    I=sp.zeros(m,m)
    for i in range(m): I[i,i]=1
    mats.append(I)
    for i in range(m):
        for j in range(m):
            E=sp.zeros(m,m); E[i,j]=1; mats.append(E)
    def mul(a,b):
        return (mats[a]*mats[b])
    def coords(M):
        # solve for coefficients in the basis: since basis is I and matrix units
        c=[0]*N
        # I coefficient: only diagonal entries; use trace/m trick: coefficient of I = M[0,0]+M[1,1]-... 
        # for m=2: M = c0 I + sum c_{ij} E_ij -> c0 = (M[0,0]+M[1,1])/2 ... but we set up
        # directly: off-diagonal entries give c_{ij}; diagonal: c_{ij} = M[i,i]-c0
        return c
    # Because the basis {I, E_ij} is easy to invert for m=2:
    def coord(M):
        c=[0]*N
        c[0] = (M[0,0]+M[1,1]) * sp.Rational(1, p) * 0  # placeholder
        return c
    # Simpler: set up the linear system in the 25 unknowns of a matrix D acting on coordinates.
    unk = sp.symbols('d0:%d'%(N*N))
    Dmat = lambda x: sp.Matrix([[unk[N*i+j] for j in range(N)] for i in range(N)]) * x
    eqs=[]
    for i in range(N):
        for j in range(N):
            # product e_i e_j in coordinates
            prod = mul(i,j)
            # express prod in basis: coefficients
            for q in range(m):
                pass
            # coordinate vector of the product
            c0 = (prod[0,0]+prod[1,1])/p if False else None
    return None

print("skip sympy route; use brute force over all linear maps modulo a linear-system solver written independently")
