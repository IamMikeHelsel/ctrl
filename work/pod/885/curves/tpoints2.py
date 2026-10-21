import json
from families import pari
from polyrows import poly_rows
d=json.load(open('poly77_lagrange.json'))
C1=pari(d['C'][1]); C2L=pari(d['C'][2]); w=pari('4*x^2+10*x+1')
quart=pari('676*x^4 - 15876*x^3 + 118461*x^2 - 333396*x + 298116')
pts=pari.hyperellratpoints(quart,2000)
ts=set()
for P in pts:
    k=P[0]
    if k**2==21: continue
    A=(12*k**2-126*k+252)/(k**2-21)
    t=A**2-144
    ts.add(str(t))
ts=sorted(ts,key=lambda s: len(s))
print(len(ts),"t values:",ts[:12])
out=[]
for ts_ in ts[:8]:
    t=pari(ts_)
    sq=[pari.issquare(t+144),pari.issquare(21*t+3969),pari.issquare(21*t+2704)]
    C2=C2L+t*w**2
    R=poly_rows([C1,C2,pari(0)],2)
    full=[X for kk,(X,s) in R.items() if len(s)==3]
    print("t",t,"squares",sq,"rows valid on {C1,C2,0}:",len(full),flush=True)
    out.append((ts_,[str(X) for X in full]))
json.dump(out,open("tfam_rows.json","w"))
