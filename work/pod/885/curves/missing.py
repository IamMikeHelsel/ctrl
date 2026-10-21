"""List the missing entries of the polynomial 7x7 Lagrange incidence with their square-free quartics."""
import sys, json
from families import pari, load
from polyrows import poly_rows
from famext import gp_sqfree
fam=sys.argv[1]; subs=dict(kv.split("=") for kv in sys.argv[2].split(","))
U,V=load(fam,subs)
R=sorted([X for X,s in poly_rows(V,2).values()],key=lambda X:(str(X) not in [str(a) for a in U]))
C=sorted([X for X,s in poly_rows(U,2).values()],key=lambda X:(str(X) not in [str(a) for a in V]))
miss={}
for i,r in enumerate(R):
    for j,c in enumerate(C):
        if not pari.issquare(r+c):
            c0,F=gp_sqfree(r+c); miss[(i,j)]=(c0,F)
            print(f"({i},{j}) c0={c0} F={pari.factor(c0*F)}")
json.dump(dict(R=[str(x) for x in R],C=[str(x) for x in C],miss={f"{i},{j}":str(c0*F) for (i,j),(c0,F) in miss.items()}),open(f"poly77_{fam}.json","w"))
