"""Incidence of polynomial rows x polynomial cols (identically square in Q[x]) and degrees of the rest."""
import sys
from families import pari, load
from polyrows import poly_rows
from famext import gp_sqfree
fam=sys.argv[1]; subs=dict(kv.split("=") for kv in sys.argv[2].split(","))
U,V=load(fam,subs)
R=[X for X,s in poly_rows(V,2).values()]
C=[X for X,s in poly_rows(U,2).values()]
# order: known first
R=sorted(R,key=lambda X:(str(X) not in [str(a) for a in U]))
C=sorted(C,key=lambda X:(str(X) not in [str(a) for a in V]))
print("rows",len(R),"cols",len(C))
for i,r in enumerate(R):
    line=[]
    for j,c in enumerate(C):
        g=r+c
        if pari.issquare(g): line.append(" ■ ")
        else:
            c0,F=gp_sqfree(g); line.append(f"{int(pari.poldegree(F)):2d} ")
    print(f"r{i}", "".join(line))
