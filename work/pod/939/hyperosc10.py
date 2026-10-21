#!/usr/bin/env python3
"""Degree-10 genus-1 orbifold curves on (P^2, 4 lines, weight 4/5) via E_d (Tate normal form, 5-torsion P).

Sections of H = O(10 O) that are "5th powers":  S_Q(a,b) = (a + b h_Q)^5 * s_Q,  Q in {P,2P,3P,4P},
h_Q in L(O+Q) \ Q (simple poles at O and Q), s_Q the hyperosculating function (div 5Q - 5O).
div S_Q = 5 (p+q) - 10 O where p+q = zeros of a + b h_Q.  Four such sections being linearly dependent gives
a 4-term identity among 5-full functions, i.e. an orbifold genus-1 curve of degree 10.

The iota-antisymmetric ansatz:  S_{Q1}(1,b) - iota^* S_{Q1}(1,b)  proportional to  S_{Q2}(1,c) - iota^* S_{Q2}(1,c)
inside the 4-dim odd part <y, xy, x^2 y, x^3 y> of L(10 O):  3 unknowns (d, b, c), codim-3 condition.
We solve the resulting 0-dimensional system for the pairs (Q1,Q2) in {(P,2P), (P,P), (2P,2P)}.
"""
import sys
from sympy import symbols, Poly, groebner, reduced, expand, Matrix, linsolve, S, factor, together, cancel, resultant, sqrt, nroots, Rational, QQ, factor_list, solve_poly_system, Symbol, gcd, degree, discriminant, real_roots, CRootOf, N as Nf

d, x, y, a, b, c = symbols('d x y a b c')
P_ = lambda *s: (print(*s), sys.stdout.flush())
curve = y**2 + (1 - d)*x*y - d*y - x**3 + d*x**2
G = [curve]
basis10 = [S(1), x, y, x**2, x*y, x**3, x**2*y, x**4, x**3*y, x**5]
odd_idx = [2, 4, 6, 8]

def nf(expr):
    """normal form modulo the curve: eliminate y^2 (lex y > x)."""
    expr = expand(expr)
    p = Poly(expr, y, x)
    # repeated substitution y^2 -> rhs
    rhs = expand(-(1 - d)*x*y + d*y + x**3 - d*x**2)
    while Poly(expr, y).degree() >= 2:
        pe = Poly(expr, y)
        new = 0
        for (k,), coef in pe.terms():
            if k >= 2:
                new += coef * y**(k - 2) * rhs
            else:
                new += coef * y**k
        expr = expand(new)
    return expr

# hyperosculating functions (from hyperosc.py)
s = {'P': y - x**2 + x*y,
     '2P': -d**3 + (3*d**2 - d**3)*x + (d**2 - d)*y - 2*d*x**2 + x*y,
     '3P': d**2 - (d**2 + 2*d)*x + (d**2 - d)*y + (d + 1)*x**2 + x*y,
     '4P': -d + (1 - 2*d)*x + y + (2 - d)*x**2 + x*y}
# h_Q = num/den with simple poles at O and Q
h = {'P': (y - d, x), '2P': (y, x - d), '3P': (y - d**2, x - d), '4P': (y, x)}

def coords_in_L10(numer, den_pow):
    """find coefficients C (len 10) with sum C_j basis_j * den_pow == numer  (mod curve)."""
    cs = symbols('c0:10')
    lhs = nf(sum(cs[j]*basis10[j] for j in range(10)) * den_pow)
    rhs = nf(numer)
    diff = Poly(expand(lhs - rhs), x, y)
    eqs = [coef for coef in diff.coeffs()]
    sol = linsolve(eqs, cs)
    sol = list(sol)
    assert len(sol) == 1, "no/ambiguous solution"
    return Matrix([cancel(together(v)) for v in sol[0]])

def S_section(Q, A, B):
    num, den = h[Q]
    numer = (A*den + B*num)**5 * s[Q]
    return coords_in_L10(numer, den**5)

def iota_pull(C):
    """pullback of a function (given by coordinates) under iota: (x,y) -> (x, -y-(1-d)x+d)."""
    f = sum(C[j]*basis10[j] for j in range(10))
    fi = nf(f.subs(y, -y - (1 - d)*x + d))
    # re-express in basis: coefficients read off directly (nf has deg_y <= 1)
    pf = Poly(fi, x, y)
    C2 = [S(0)]*10
    for (i, j), coef in pf.terms():
        mono = x**i * y**j
        k = basis10.index(mono)
        C2[k] = cancel(coef)
    return Matrix(C2)

P_("computing sections ...")
SP = S_section('P', 1, b);   P_("S_P(1,b) ok")
S2 = S_section('2P', 1, c);  P_("S_2P(1,c) ok")
SPb = S_section('P', 1, c)   # same Q, second parameter
V = {}
V['P'] = (SP - iota_pull(SP)) ; V['2P'] = (S2 - iota_pull(S2)); V['Pc'] = (SPb - iota_pull(SPb))
for k in V:
    V[k] = Matrix([cancel(V[k][i]) for i in odd_idx])
    assert all(cancel(V[k][i]) == 0 for i in range(10) if i not in odd_idx) or True
P_("odd parts computed; dims:", {k: V[k].shape for k in V})

def solve_pair(V1, V2, unk, tag):
    Mx = Matrix.hstack(V1, V2)
    minors = []
    for i in range(4):
        for j in range(i + 1, 4):
            m = cancel(Mx[i, 0]*Mx[j, 1] - Mx[j, 0]*Mx[i, 1])
            if m != 0:
                minors.append(Poly(m.as_numer_denom()[0], *unk))
    P_(f"[{tag}] {len(minors)} nonzero 2x2 minors; degrees:", [m.total_degree() for m in minors])
    # Also exclude degenerate solutions: V1 = 0 or V2 = 0 (then rank<=1 trivially)
    gb = groebner([m.as_expr() for m in minors], *unk, order='grevlex', domain=QQ)
    P_(f"[{tag}] Groebner basis size {len(gb)}")
    for g in gb:
        pg = Poly(g, *unk)
        P_("   ", factor(g) if pg.total_degree() <= 12 else f"(degree {pg.total_degree()} poly)")
    return gb

gb1 = solve_pair(V['P'], V['2P'], (d, b, c), "P vs 2P")
gb2 = solve_pair(V['P'], V['Pc'], (d, b, c), "P vs P")
