"""Independent exact re-check (sympy, no PARI) of the Klein-class K1 polynomial 7x7 (poly77_v1.json):
counts R_i + C_j that are perfect squares in Q[x], lists a 4x4 biclique, and checks it is
nondegenerate (distinct rows, distinct columns) and specialises to a valid rational 4x4 grid.
"""
import json
from fractions import Fraction as F
from itertools import combinations
import sympy as sp

x = sp.symbols("x")
d = json.load(open("poly77_v1.json"))
R = [sp.Poly(sp.sympify(s.replace("^", "**")), x, domain="QQ") for s in d["R"]]
C = [sp.Poly(sp.sympify(s.replace("^", "**")), x, domain="QQ") for s in d["C"]]


def is_square(p):
    if p.is_zero:
        return True
    c, facs = p.sqf_list()
    return sp.sqrt(sp.Rational(c)).is_rational and all(e % 2 == 0 for _, e in facs)


inc = {(i, j): is_square(r + c) for i, r in enumerate(R) for j, c in enumerate(C)}
print("square incidences:", sum(inc.values()), "of", len(R) * len(C))
assert len({str(r) for r in R}) == len(R) and len({str(c) for c in C}) == len(C)
found = None
for rows in combinations(range(len(R)), 4):
    cols = [j for j in range(len(C)) if all(inc[i, j] for i in rows)]
    if len(cols) >= 4:
        found = (rows, cols[:4])
        break
print("4x4 biclique rows", found[0], "cols", found[1])
for x0 in (sp.Rational(k) for k in (2, 3, 5, 7, 11)):
    U = [F(str(R[i].eval(x0))) for i in found[0]]
    V = [F(str(C[j].eval(x0))) for j in found[1]]
    if len(set(U)) == 4 and len(set(V)) == 4:
        break
for u in U:
    for v in V:
        s = u + v
        n, m = s.numerator, s.denominator
        assert n >= 0 and sp.sqrt(n).is_integer and sp.sqrt(m).is_integer, (u, v)
assert len(set(U)) == 4 and len(set(V)) == 4
print(f"x={x0} rational 4x4: U =", [str(u) for u in U], "V =", [str(v) for v in V], "all 16 sums squares")
