"""m5: q:noncomm (line 458) is false -- H (real quaternions) with alpha = id.

alpha = id is an involutive automorphism of H, inner with D = 1, so
mu_alpha(x,y) = xy + alpha(yx) = xy + yx = the Jordan product.  By rem:inner's
own (correct) equivalence, "H is determined by mu_alpha" <=> "H is zJpd".
As in Bresar 2021, Example 3.19 (PDF pp. 61-62 = printed pp. 53-54), H is not
zJpd; the two computational ingredients are checked here.

Quaternions: x = (a, v), a in Q, v in Q^3,
   (a,v)(b,w) = (ab - v.w, a w + b v + v x w),
whence (a,v) o (b,w) = (2(ab - v.w), 2(a w + b v)).
"""
from fractions import Fraction as F
import random

import sympy as sp


def mul(x, y):
    a, v = x
    b, w = y
    dot = sum(F(vi) * wi for vi, wi in zip(v, w))
    cross = (v[1] * w[2] - v[2] * w[1], v[2] * w[0] - v[0] * w[2], v[0] * w[1] - v[1] * w[0])
    return (a * b - dot, tuple(a * wi + b * vi + ci for vi, wi, ci in zip(v, w, cross)))


def jor(x, y):
    p, q = mul(x, y), mul(y, x)
    return (p[0] + q[0], tuple(pi + qi for pi, qi in zip(p[1], q[1])))


def phi(x, y):
    return x[0] * y[0]


Z = (F(0), (F(0), F(0), F(0)))
ONE = (F(1), (F(0), F(0), F(0)))
I = (F(0), (F(1), F(0), F(0)))
J = (F(0), (F(0), F(1), F(0)))

print("=== 0. sanity: i o j = 0 with i, j both nonzero ===")
print("  i o j =", jor(I, J), " phi(i,j) =", phi(I, J))

print("\n=== 1. the exact failure of condition (ii) of Bresar Prop. 1.3 ===")
lhs = (jor(ONE, ONE)[0] + jor(I, I)[0], tuple(
    a + b for a, b in zip(jor(ONE, ONE)[1], jor(I, I)[1])))
print("  (1,0)o(1,0) + (0,i)o(0,i) =", lhs, "(zero:", lhs == Z, ")")
print("  phi((1,0),(1,0)) + phi((0,i),(0,i)) =", phi(ONE, ONE) + phi(I, I), "(nonzero)")

print("\n=== 2. symbolic proof that x o y = 0 forces phi(x,y) = 0 ===")
a, b = sp.symbols('a b', real=True)
x1, x2, x3, y1, y2, y3 = sp.symbols('x1 x2 x3 y1 y2 y3', real=True)
xv = sp.Matrix([x1, x2, x3])
yv = sp.Matrix([y1, y2, y3])
eq1 = a * b - (xv.T * yv)[0]          # scalar part of x o y
eq2 = a * yv + b * xv                 # vector part of x o y (the cross terms cancel)
ident = sp.expand((xv.T * eq2)[0] - b * (a ** 2 + (xv.T * xv)[0]) + a * eq1)
print("  x.(a y + b x) - b(a^2 + |x|^2) + a(ab - x.y) =", ident)
print("  so on x o y = 0 one gets b(a^2+|x|^2) = 0; over R this forces b = 0 unless x = 0.")
print("  Symmetrically a(b^2+|y|^2) = 0.  Hence a = 0 or b = 0, so phi = ab = 0.")

print("\n=== 3. random exact test: phi vanishes on every anticommuting pair found ===")
random.seed(1)
bad = tested = nonzero_both = 0
for _ in range(400000):
    x = (F(random.randint(-3, 3)), tuple(F(random.randint(-3, 3)) for _ in range(3)))
    y = (F(random.randint(-3, 3)), tuple(F(random.randint(-3, 3)) for _ in range(3)))
    if jor(x, y) == Z:
        tested += 1
        if x != Z and y != Z:
            nonzero_both += 1
        if phi(x, y) != 0:
            bad += 1
print(f"  anticommuting pairs found: {tested} (with both entries nonzero: {nonzero_both});"
      f" phi != 0 in {bad} of them")

print("\n=== 4. conclusion ===")
print("  H is not zJpd (Prop. 1.3(ii) fails for phi), hence by rem:inner's equivalence")
print("  H is not determined by mu_alpha for the inner involutive automorphism alpha = id.")
print("  Line 458 of the paper ('the answer is affirmative, in characteristic other than 2,")
print("  whenever alpha is inner') is therefore false.")
