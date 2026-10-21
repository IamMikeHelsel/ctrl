#!/usr/bin/env python3
"""Low-genus curves on the twisted Fermat quintic surfaces S_c : x^5 + y^5 = c (w^5 - z^5), c>0.

These are exactly the diagonal quintic surfaces a x^5 + b y^5 + c z^5 = d w^5 that contain a rational
line (need -b/a and d/c to be 5th powers; WLOG a=b, c=d).  Positive rational points give
A+B+C=D with A=x^5, B=y^5, C=c z^5, D=c w^5 (5-full once rad(c) | z,w).

Pencil of planes through the line L = {x=-y, w=z}:  P_mu : x + y = mu (w - z).
Section = L + residual plane quartic Q_mu.  Q_mu is singular at p (off L) iff T_p S contains L,
iff x0^4 = y0^4 and z0^4 = w0^4.  Output: the mu-values, number of nodes, explicit check for c=4,
and the positivity obstruction.
"""
import sys, itertools
from sympy import symbols, I, expand, factor, simplify, Poly, groebner, S, cancel, factor_list, QQ, sqrt

x, y, z, w, c, mu = symbols('x y z w c mu')
F = x**5 + y**5 - c*(w**5 - z**5)
G = [F.diff(v) for v in (x, y, z, w)]
P = lambda *a: (print(*a), sys.stdout.flush())

P("contact points of tangent planes containing L (r = y0/x0, s = w0/z0, r^4=s^4=1):")
results = {}
for r in (1, -1, I, -I):
    for s in (1, -1, I, -I):
        r, s = S(r), S(s)
        if simplify(1 + r**5) == 0 or simplify(s - 1) == 0:
            P(f"  r={r}, s={s}: contact point lies on L (degenerate)"); continue
        t5 = simplify(c*(s**5 - 1)/(1 + r**5))                  # x0^5/z0^5
        mu5 = simplify(((1 + r)/(s - 1))**5 * t5)                # mu = (x0+y0)/(w0-z0)
        x0, z0 = symbols('x0 z0')
        g = [gi.subs({x: x0, y: r*x0, z: z0, w: s*z0}) for gi in G]
        P(f"  r={str(r):>3}, s={str(s):>3}:  mu^5 = {mu5}   [grad.(1,-1,0,0), grad.(0,0,1,1)] = {simplify(g[0]-g[1])}, {simplify(g[2]+g[3])}")
        results.setdefault(str(mu5), []).append((r, s))
P("\nmu^5 values -> number of contact points (= singular points of residual quartic Q_mu off L):")
for k, v in results.items():
    P(f"  mu^5 = {k}: {len(v)} nodes  -> geometric genus of Q_mu <= {3 - len(v)}")

# Explicit: c = 4, mu = -1 (mu^5 = -c/4).  Predicted nodes: (x,y,z,w) = (1-i, 1+i, 1, -1) and conjugate.
P("\n--- explicit: c=4, mu=-1, plane x + y = -(w - z) ---")
Fsub = expand(F.subs(c, 4).subs(x, -y - (w - z)))
Q = cancel(Fsub/(w - z))
P("residual quartic Q(y,z,w) =", expand(Q))
fl = factor_list(Q)
P("factorisation over Q:", fl)
fl_i = factor_list(Q, extension=I)
P("factorisation over Q(i):", fl_i)
for pt in [(1 + I, 1, -1), (1 - I, 1, -1)]:
    sub = dict(zip((y, z, w), pt))
    vals = [simplify(expand(e.subs(sub))) for e in (Q, Q.diff(y), Q.diff(z), Q.diff(w))]
    P(f"  at (y,z,w)={pt}: Q, Q_y, Q_z, Q_w = {vals}")
# all singular points via Groebner basis of Jacobian ideal, affine chart w=1 (and check the line w=0)
Ja = [expand(e.subs(w, 1)) for e in (Q.diff(y), Q.diff(z), Q.diff(w))]
gb = groebner(Ja, y, z, order='lex', domain=QQ)
P("Groebner basis (lex, w=1) of singular locus:", list(gb))
Jinf = [expand(e.subs(w, 0)) for e in (Q.diff(y), Q.diff(z), Q.diff(w), Q)]
gb0 = groebner(Jinf, y, z, order='lex', domain=QQ)
P("Groebner basis of singular locus on w=0:", list(gb0))

# Positivity obstruction for mu<0.
P("\nPositivity: plane x+y = mu(w-z), mu<0.  Sign patterns (ex,ey,ez,ew) where the odd-one-out term of")
P("x^5+y^5+c z^5-c w^5 coincides with the odd-one-out of x+y+|mu|z-|mu|w (necessary for A+B+C=D with all >0):")
def odd(t):
    pos = [i for i in range(4) if t[i] > 0]; neg = [i for i in range(4) if t[i] < 0]
    return pos[0] if len(pos) == 1 else (neg[0] if len(neg) == 1 else None)
ok = [s_ for s_ in itertools.product([1, -1], repeat=4)
      if odd((s_[0], s_[1], s_[2], -s_[3])) is not None and odd((s_[0], s_[1], s_[2], -s_[3])) == odd((s_[0], s_[1], -s_[2], s_[3]))]
P("compatible patterns:", ok, "(empty => no positive solutions on any plane with mu<0)")
