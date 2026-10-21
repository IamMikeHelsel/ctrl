#!/usr/bin/env python3
"""4-term relations among hyperosculating functions on elliptic curves with a 5-torsion point.

E_d (Tate normal form): y^2 + (1-d) x y - d y = x^3 - d x^2,  P=(0,0) of order 5,
2P=(d,d^2), 3P=(d,0), 4P=(0,d).
L(5O) = <1, x, y, x^2, xy>.  For p in E[5], s_p in L(5O) has divisor 5p - 5O (unique up to scalar).
The five functions s_O=1, s_P, s_2P, s_3P, s_4P are T_P^b-translates of 1 in the Heisenberg sense, so
rank span{s_bP} = #{i : a_i != 0} where 1 = sum a_i e_i in the translation eigenbasis.
Four of them are linearly dependent  <=>  rank <= 3.  A 4-term dependency gives a polynomial identity
sum_b c_b S_b(X,Y,Z) = 0 among weighted-homogeneous forms with 5-fold divisors: a genus-1 orbifold
curve on (P^2, 4 lines, weight 4/5) -- i.e. a candidate infinite family for Erdos 939, r=5.
"""
import sys
from sympy import symbols, Matrix, series, solve, Poly, factor, simplify, Rational, S, together, cancel, sqrt, nroots, roots, factor_list, QQ, expand, degree

d, x, y, u = symbols('d x y u')
Ecurve = y**2 + (1 - d)*x*y - d*y - (x**3 - d*x**2)
basis = [S(1), x, y, x**2, x*y]
P_ = lambda *a: (print(*a), sys.stdout.flush())

def local_y(xp, yp, order=6):
    """power series y(u) around p=(xp,yp) with x = xp+u (x is a local parameter at the 5-torsion points)."""
    # solve E(xp+u, y)=0 for y as series: Newton iteration on series
    Y = S(yp)
    for k in range(1, order + 1):
        # Y = Y - E/E_y evaluated, truncated at u^order
        expr = Ecurve.subs({x: xp + u, y: Y})
        dexpr = Ecurve.diff(y).subs({x: xp + u, y: Y})
        Y = series(Y - expr/dexpr, u, 0, order + 1).removeO()
        Y = expand(Y)
    return Y

def hyperosc_vector(xp, yp):
    Y = local_y(xp, yp)
    cols = []
    for b in basis:
        e = expand(b.subs({x: xp + u, y: Y}))
        e = series(e, u, 0, 5).removeO()
        cols.append([expand(e).coeff(u, k) for k in range(5)])
    A = Matrix(cols).T          # 5 x 5 : rows = coefficient of u^k, cols = basis functions
    # vanishing to order 5: first 5 coefficients zero -> kernel of 5x5 matrix (rank 4 generically)
    ker = A.nullspace()
    assert len(ker) == 1, f"kernel dim {len(ker)} at p=({xp},{yp})"
    v = ker[0]
    v = v / v[[i for i in range(5) if v[i] != 0][-1]]   # normalise
    return Matrix([cancel(together(c)) for c in v])

pts = {'O': None, 'P': (0, 0), '2P': (d, d**2), '3P': (d, 0), '4P': (0, d)}
vecs = {'O': Matrix([1, 0, 0, 0, 0])}
for k, p in pts.items():
    if p is None: continue
    vecs[k] = hyperosc_vector(*p)
    P_(f"s_{k} = coefficients in <1,x,y,x^2,xy>: {list(vecs[k].T)}")

M = Matrix.hstack(*[vecs[k] for k in ['O', 'P', '2P', '3P', '4P']])
detM = factor(cancel(M.det()))
P_("\ndet M(d) =", detM)
# rank-3 locus: all 4x4 minors vanish.  By Heisenberg + iota symmetry, rank is 5, 4 (a_0=0), 3 (a_1 or a_2 = 0), ...
# Compute gcd of all 4x4 minors (numerators).
from sympy import gcd as sgcd
from itertools import combinations
minors = []
for rows in combinations(range(5), 4):
    for cols in combinations(range(5), 4):
        m = M.extract(list(rows), list(cols)).det()
        m = cancel(together(m))
        if m != 0:
            minors.append(Poly(m.as_numer_denom()[0], d))
g = minors[0]
for m in minors[1:]:
    g = sgcd(g, m)
P_("gcd of numerators of all 4x4 minors (rank<=3 locus):", factor(g.as_expr()))
num = Poly(detM.as_numer_denom()[0], d)
P_("roots of det M (rank<=4 locus):", factor_list(num.as_expr()))
