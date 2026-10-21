"""Calibrate vsearch2's plane_rows/generic_rows on Lagrange's E_B (expect 6 plane + 1 generic)."""
import json
from fractions import Fraction as F
from klein import roots, invol, mob, pari
from vsearch2 import plane_rows, generic_rows, PAIR

d = json.load(open("poly77_lagrange.json"))
C = [c for c in d["C"] if c != "0"]
C1, C2 = C[1], C[2]
r = roots(C1)
s1, s2 = invol(r[0], r[1], r[2], r[3]), invol(r[0], r[2], r[1], r[3])
o1 = [r[0], mob(s1, r[0]), mob(s2, r[0]), mob(s1, mob(s2, r[0]))]
r2 = roots(C2)
u = r2[0]
o2 = [u, mob(s1, u), mob(s2, u), mob(s1, mob(s2, u))]
assert set(o2) == set(r2), (o2, r2)
c1 = F(str(pari.pollead(pari(C1))))
c2 = F(str(pari.pollead(pari(C2))))
print("o1", o1, "o2", o2, "c1", c1, "c2", c2)
tot = 0
for k in range(3):
    rr = plane_rows(o1, o2, k, c1, c2)
    print("plane", k, rr)
    tot += len(rr or [])
g = generic_rows(o1, o2, c1, c2)
print("generic", g)
print("total", tot + len(g))
print("known rows", d["R"])
