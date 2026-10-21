import json, time
from fractions import Fraction as F
from numext import extend
g=json.load(open("grids/g64_lagrange_m911_588.json"))
U=[F(x) for x in g["U"]]; V=[F(x) for x in g["V"]]
for N in (1,2):
    t=time.time()
    o=extend(U,V,N)
    print("N",N,"newrows",len(o["rows"]),"newcols",len(o["cols"]),"grids",[(a,len(b),len(c)) for a,b,c in o["grids"]], time.time()-t, flush=True)
    for r,(T,n) in o["rows"].items(): print(" row",T,n,str(r)[:80])
    for c,(T,n) in o["cols"].items(): print(" col",T,n,str(c)[:80])
