"""Independent verification (m5) of the three M2F3Check #guards in
lean/Research/BraidedSymZpd/BraidedSymZpd.lean, plus the two side claims of
prop:matrix.  Pure python, no shared code with the Lean file."""
import itertools

def make(p):
    els = [ (a,b,c,d) for a in range(p) for b in range(p) for c in range(p) for d in range(p) ]
    def mul(x,y):
        return ((x[0]*y[0]+x[1]*y[2])%p, (x[0]*y[1]+x[1]*y[3])%p,
                (x[2]*y[0]+x[3]*y[2])%p, (x[2]*y[1]+x[3]*y[3])%p)
    def add(x,y): return tuple((a+b)%p for a,b in zip(x,y))
    def scal(c,x): return tuple((c*a)%p for a in x)
    return els, mul, add, scal

def conj_alpha(x):            # conjugation by diag(1,-1)
    a,b,c,d = x
    return (a, (-b)%3, (-c)%3, d)

def trans_alpha(x):           # transpose
    a,b,c,d = x
    return (a,c,b,d)

def rank(rows, n, p):
    basis, piv = [], []
    for r0 in rows:
        r = list(r0)
        for i,b in enumerate(basis):
            f = r[piv[i]] % p
            if f:
                r = [ (rj - f*bj) % p for rj,bj in zip(r,b) ]
        nz = next((j for j in range(n) if r[j] % p), None)
        if nz is not None:
            s = pow(r[nz], p-2, p)
            r = [ (t*s) % p for t in r ]
            basis.append(r); piv.append(nz)
    return len(basis)

def report(name, p, mu, els, add):
    n = 4
    tens = lambda x,y: tuple((x[i]*y[j])%p for i in range(n) for j in range(n))
    zero = [tens(x,y) for x,y in itertools.product(els,els) if mu(x,y)==(0,0,0,0)]
    nzero = len(zero)
    dimZ = rank(zero, n*n, p)
    basisE = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
    muRows = [mu(x,y) for x in basisE for y in basisE]
    rk = rank(muRows, n, p)
    print(f"{name}: #zero pairs={nzero}, dim Z_mu={dimZ}, rank mu_bar={rk}, dim ker mu_bar={n*n-rk}"
          f"  -> determined (Z=ker) : {dimZ == n*n-rk}")
    return nzero, dimZ, rk

els, mul, add, scal = make(3)
def mu_twist(x,y):
    return add(mul(x,y), conj_alpha(mul(y,x)))
def mu_prod(x,y): return mul(x,y)
def mu_trans(x,y):
    return add(mul(x,y), trans_alpha(mul(y,x)))
def mu_trans2(x,y):
    # the paper's "twist by the transpose, taken with the braiding product xy + y^T x^T"
    a = mul(x,y)
    yt = (y[0],y[2],y[1],y[3]); xt = (x[0],x[2],x[1],x[3])
    return add(a, mul(yt,xt))

r1 = report("M2(F3), mu = xy + conj_alpha(yx)   [prop:matrix]", 3, mu_twist, els, add)
r2 = report("M2(F3), ordinary product            [side claim]", 3, mu_prod, els, add)
r3 = report("M2(F3), xy + (yx)^T                 [side claim]", 3, mu_trans, els, add)
r4 = report("M2(F3), xy + y^T x^T                [side claim]", 3, mu_trans2, els, add)
print()
print("guard 1 (zeroPairs.length == 417):", r1[0] == 417)
print("guard 2 (rank zeroPairs 16 == 12):", r1[1] == 12)
print("guard 3 (rankMu == 4):", r1[2] == 4)
print("Lean-encoded product == paper's mu_alpha(x,y)=xy+alpha(yx):",
      all(mu_twist(*xy) == (lambda x,y: add(mul(x,y), conj_alpha(mul(y,x))))(*xy)
          for xy in itertools.product(els,els)))
