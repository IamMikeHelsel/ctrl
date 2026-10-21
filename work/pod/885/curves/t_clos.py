import time, json
from families import pari
import polyrows
P=json.load(open("poly77_lagrange.json"))
C=[pari(s) for s in P["C"]]
orig=polyrows.solve_pair
cnt=[0]
def sp(*a):
    cnt[0]+=1
    t=time.time(); r=orig(*a); dt=time.time()-t
    if dt>1: print("slow solve_pair",dt,flush=True)
    return r
polyrows.solve_pair=sp
t=time.time()
for a in range(7):
    for j in range(7):
        if j!=a:
            d=C[j]-C[a]
            print(a,j,pari.factor(d)[0].length(), [int(pari.poldegree(f)) for f in pari.factor(d)[0]], flush=True)
    break
R=polyrows.poly_rows(C,2)
print("rows",len(R),time.time()-t,cnt)
