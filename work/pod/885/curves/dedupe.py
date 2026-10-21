"""Canonical integer forms of found grids; dedupe; independent exact re-verification."""
import sys, json, re
from fractions import Fraction as F
from math import gcd
from functools import reduce
from verify_grid import check_grid, integer_form, D_member

def canon(U, V):
    """6x4 / 4x6 -> canonical (Ns, ds) of the 5-N/4-d form, primitive (no common square factor)."""
    U=[F(u) for u in U]; V=[F(v) for v in V]
    if len(U) < len(V): U, V = V, U
    Ns, ds = integer_form(U, V)
    # remove common factor k^2 from N and k from d
    g = reduce(gcd, ds)
    k = 1
    for p in range(2, int(g**0.5)+2):
        pass
    # largest k with k|all d and k^2|all N
    best=1
    for k in range(1, min(g, 10**6)+1):
        if g % k == 0 and all(n % (k*k) == 0 for n in Ns):
            best = k
    Ns=[n//(best*best) for n in Ns]; ds=[d//best for d in ds]
    return tuple(sorted(Ns)), tuple(sorted(ds))

seen={}
for path in sys.argv[1:]:
    for line in open(path):
        if not line.startswith("GRID"): continue
        js=json.loads(line[line.index("{"):])
        U,V=js["U"],js["V"]
        check_grid([F(u) for u in U],[F(v) for v in V])
        c=canon(U,V)
        for n in c[0]:
            for d in c[1]:
                assert D_member(n,d)
        x=re.search(r"x=(\S+)",line).group(1)
        seen.setdefault(c,[]).append((line.split()[1],x))
print(len(seen),"distinct configurations")
for c,v in sorted(seen.items(), key=lambda t: max(t[0][0])):
    print(f"N={list(c[0])} d={list(c[1])}  from {v[:4]}")
