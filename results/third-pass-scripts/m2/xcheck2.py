"""Independent check of dim Der(M_2(F_p)) by solving the linear system with a
*different* implementation: Nullspace of the Jacobi-style conditions on the
left/right multiplication representation, using sympy's Matrix over GF(p)."""
import sympy as sp
from build import from_mats, full_matrix_units
from alg import Alg
from linmod import nullspace, rank

def der_by_conditions(p, mats):
    """Solve D(xy)=D(x)y+xD(y) directly on matrices (unknowns = images of basis)."""
    n=len(mats); s=len(mats[0])
    # unknown: D(e_j) = sum_k u[j][k] e_k, j in 0..n-1, k in 0..n-1 -> n*n unknowns
    N=n*n
    rows=[]
    for i in range(n):
        for j in range(n):
            # product e_i e_j as a matrix
            prod=[[sum(mats[i][a][b]*mats[j][b][c] for b in range(s))%p for c in range(s)] for a in range(s)]
            # for each coordinate (a,b) produce a linear equation in the unknowns
            for a in range(s):
                for b in range(s):
                    row=[0]*N
                    # LHS: D(prod) = sum_k coord_k(prod) * sum_l u[k][l] * mats[l][a][b]
                    # first express prod in the basis
                    coeff=[0]*n
                    # solve prod = sum coeff_k mats[k] by elimination (independent method: use lstsq style)
                    # we know the basis is I,E_ij so read off:
                    for k in range(n):
                        coeff[k]=None
                    # generic solve
                    A=[[mats[k][x][y] for k in range(n)] for x in range(s) for y in range(s)]
                    rhs=[prod[x][y] for x in range(s) for y in range(s)]
                    sol=sp.Matrix(A).gauss_jordan_solve(sp.Matrix(rhs), sp.Symbol('t'))[0] if False else None
                    # do a simple modular solve
                    M=[[ (A[r][c]%p) for c in range(n)]+[rhs[r]%p] for r in range(len(A))]
                    r=0; piv=[]
                    for c in range(n):
                        pr=-1
                        for i2 in range(r,len(M)):
                            if M[i2][c]%p: pr=i2; break
                        if pr<0: continue
                        M[r],M[pr]=M[pr],M[r]
                        inv=pow(M[r][c],p-2,p)
                        M[r]=[(x*inv)%p for x in M[r]]
                        for i2 in range(len(M)):
                            if i2!=r and M[i2][c]%p:
                                f=M[i2][c]
                                M[i2]=[(x-f*y)%p for x,y in zip(M[i2],M[r])]
                        piv.append(c); r+=1
                        if r==len(M): break
                    cs=[0]*n
                    for i2,c in enumerate(piv): cs[c]=M[i2][n]
                    # LHS coefficients: for unknown (k,l): cs[k]*mats[l][a][b]
                    for k in range(n):
                        for l in range(n):
                            row[k*n+l]=(row[k*n+l]+cs[k]*mats[l][a][b])%p
                    # RHS: D(e_i)e_j + e_i D(e_j): unknown (i,l) coefficient mats[l]·e_j ; unknown (j,l): e_i·mats[l]
                    for l in range(n):
                        # (D(e_i)) e_j = mats[l]*mats[j]
                        prod2=[[sum(mats[l][x][y]*mats[j][y][z] for y in range(s))%p for z in range(s)] for x in range(s)]
                        row[i*n+l]=(row[i*n+l]-prod2[a][b])%p
                        prod3=[[sum(mats[i][x][y]*mats[l][y][z] for y in range(s))%p for z in range(s)] for x in range(s)]
                        row[j*n+l]=(row[j*n+l]-prod3[a][b])%p
                    rows.append([x%p for x in row])
    return len(nullspace(rows,p,N))

for p in (2,3,5):
    mats=full_matrix_units(p,2)
    print("M_2(F_%d): independent dim Der ="%p, der_by_conditions(p,mats))
    A=from_mats(p,mats,"M2")
    print("           alg.py dim Der =", len(A.derivations()))
