"""Finite algebras over F_p by structure constants; zpd test for an arbitrary bilinear mu:
   A determined by mu  <=>  dim span{x(x)y : mu(x,y)=0} == dim ker mu-bar   (paper's cor:criterion)."""
import itertools

def rank(rows,D,p):
    basis={}
    for r in rows:
        r=list(r)
        for i in range(D):
            if r[i]%p:
                if i in basis:
                    f=r[i]; b=basis[i]
                    r=[(x-f*y)%p for x,y in zip(r,b)]
                else:
                    f=pow(r[i],p-2,p); basis[i]=[(x*f)%p for x in r]
                    break
    return len(basis)

def kernel(imgs,d,p):
    """imgs[j] = image of e_j under a linear map F_p^d -> F_p^d; return basis of the kernel."""
    M=[[imgs[j][i]%p for j in range(d)] for i in range(d)]   # M[i][j]
    piv=[]; r=0
    for c in range(d):
        pr=None
        for i in range(r,d):
            if M[i][c]%p: pr=i; break
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]
        f=pow(M[r][c],p-2,p); M[r]=[(x*f)%p for x in M[r]]
        for i in range(d):
            if i!=r and M[i][c]%p:
                f=M[i][c]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==d: break
    free=[c for c in range(d) if c not in piv]
    out=[]
    for fc in free:
        v=[0]*d; v[fc]=1
        for i,pc in enumerate(piv): v[pc]=(-M[i][fc])%p
        out.append(tuple(v))
    return out

class Alg:
    def __init__(self,d,p,mult,one=None,name=""):
        self.d=d; self.p=p; self.mult=mult; self.one=one; self.name=name
        self.els=list(itertools.product(range(p),repeat=d))
        self.bas=[tuple(1 if i==j else 0 for i in range(d)) for j in range(d)]
    def comb(self,coefs,vs):
        p=self.p; out=[0]*self.d
        for f,v in zip(coefs,vs):
            if f%p:
                for k in range(self.d):
                    if v[k]: out[k]=(out[k]+f*v[k])%p
        return tuple(out)
    def m(self,x,y):
        p=self.p
        return self.comb([x[i]*y[j]%p for i in range(self.d) for j in range(self.d)],
                         [self.mult[i][j] for i in range(self.d) for j in range(self.d)])
    def mu_el(self,x,y,mu):
        if mu is None: return self.m(x,y)
        p=self.p
        return self.comb([x[i]*y[j]%p for i in range(self.d) for j in range(self.d)],
                         [mu(self.bas[i],self.bas[j]) for i in range(self.d) for j in range(self.d)])
    def mu_rank(self,mu=None):
        return rank([self.mu_el(self.bas[i],self.bas[j],mu) for i in range(self.d) for j in range(self.d)],self.d,self.p)
    def z_dim(self,mu=None):
        p=self.p; d=self.d; D=d*d; tens=[]
        for x in self.els:
            imgs=[self.mu_el(x,self.bas[j],mu) for j in range(d)]
            for k in kernel(imgs,d,p):
                t=[0]*D
                for i in range(d):
                    if x[i]:
                        for j in range(d):
                            if k[j]: t[i*d+j]=(t[i*d+j]+x[i]*k[j])%p
                tens.append(tuple(t))
        return rank(tens,D,p)
    def determined(self,mu=None):
        D=self.d*self.d
        return self.z_dim(mu)==D-self.mu_rank(mu), self.z_dim(mu), D-self.mu_rank(mu)

def matrix_units_alg(n,p):
    d=n*n; idx=lambda i,j:i*n+j
    mult=[[None]*d for _ in range(d)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    v=[0]*d
                    if j==k: v[idx(i,l)]=1
                    mult[idx(i,j)][idx(k,l)]=tuple(v)
    one=tuple(1 if any(idx(i,i)==t for i in range(n)) else 0 for t in range(d))
    return Alg(d,p,mult,one,"M_%d(F_%d)"%(n,p))
