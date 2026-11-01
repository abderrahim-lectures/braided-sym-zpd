"""Counterexample to the sentence in q:noncomm (paper line 458):
   'the answer is affirmative, in characteristic other than 2, whenever alpha is inner'.

A = H, the real quaternions (noncommutative, unital, char 0). alpha = id, which is an
involutive automorphism and is inner (D = 1). Then the twisted product is
    mu_alpha(x,y) = xy + alpha(yx) = xy + yx = x o y,
the Jordan product, so 'determined by mu_alpha' is exactly 'zJpd', and Brešar (2021),
Example 3.19, pp. 53-54 shows H is not zJpd.  The witness is reproduced below with sympy.
"""
import sympy as sp

a, b, c, d, e, f, g, h = sp.symbols('a b c d e f g h', real=True)
I2 = sp.eye(2)
# H as 2x2 complex matrices: (a,x) |-> a I + x1 i sigma_z? use Pauli: i->s1*i? simplest:
# represent (a; x1,x2,x3) as a*I + i*(x1*sx + x2*sy + x3*sz)  (a standard real rep)
# 1 -> I,  i -> diag(i,-i),  j -> [[0,1],[-1,0]],  k -> [[0,i],[i,0]]
Mi = sp.Matrix([[sp.I, 0], [0, -sp.I]])
Mj = sp.Matrix([[0, 1], [-1, 0]])
Mk = sp.Matrix([[0, sp.I], [sp.I, 0]])
def H(v):  # v = (a,x1,x2,x3)
    return v[0]*I2 + v[1]*Mi + v[2]*Mj + v[3]*Mk

one = (1, 0, 0, 0)
ii = (0, 1, 0, 0)
def mul(u, v):  # (alpha,x)(beta,y) = (alpha beta - x.y, alpha y + beta x + x cross y)
    al, x = u[0], sp.Matrix(u[1:])
    be, y = v[0], sp.Matrix(v[1:])
    return (sp.simplify(al*be - (x.T*y)[0]),) + tuple(sp.simplify(al*y + be*x + x.cross(y)))
def jor(u, v):
    p, q = mul(u, v), mul(v, u)
    return tuple(sp.simplify(p[k]+q[k]) for k in range(4))

# the matrix representation agrees with the formula on the four basis elements
BASIS4 = [one, ii, (0,0,1,0), (0,0,0,1)]
for u in BASIS4:
  for v in BASIS4:
    assert sp.simplify(H(mul(u, v)) - H(u)*H(v)) == sp.zeros(2, 2), (u, v)
print('2x2 complex matrix representation matches the quaternion product on all 16 basis pairs')

print('1 o 1 =', jor(one, one), '   i o i =', jor(ii, ii))
print('sum      =', tuple(sp.simplify(jor(one, one)[k] + jor(ii, ii)[k]) for k in range(4)))
# Brešar's functional phi((al,x),(be,y)) = al*be
phi = lambda u, v: sp.simplify(u[0]*v[0])
print('phi(1,1) + phi(i,i) =', sp.simplify(phi(one, one) + phi(ii, ii)))
# phi vanishes on the anticommuting pair (1,i): 1 o i = ?
print('1 o i =', jor(one, ii), ' phi(1,i) =', phi(one, ii))
print()
print('So sum of Jordan products is 0 but the sum of phi values is 1:')
print('condition (ii) of Brešar Proposition 1.3 fails, hence H is not zJpd,')
print('hence H is not determined by x o y = mu_alpha with alpha = id (inner, involutive).')
