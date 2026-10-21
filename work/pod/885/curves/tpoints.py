import sys
from sfam import data, pari
from deform2 import solve, polys, rationalise
def t_of_k(k):
    k=pari(k); m=-(-179*k**2+1260*k+311661)/(39*k**2-154791)
    return (-1248*m+5728)/(m**2-21)
ts=[]
for k in ["0","1","2","-1","1/2","3","5","-3","10"]:
    t=t_of_k(k); ts.append(t)
    d1=21*(t+189)*(21*t+2704); d2=(t+144)*(21*t+2704)
    print(k, t, pari.issquare(d1), pari.issquare(d2))
for t in ts[:5]:
    o,z=data(t-9072)
    q,bad=rationalise(z, bound=10**40, eps="1e-150")
    print("t",t,"res",o["res"],"non-rational coords:",bad, flush=True)
