import time
from ext import pari
from ecgrid import curve
from math import gcd
t=time.time(); hist={}
n=0
for b in range(100,130):
    for a in range(1,b):
        if gcd(a,b)>1: continue
        r=pari.ellrank(curve(0,a,b)); lo=int(r[0]); hist[lo]=hist.get(lo,0)+1; n+=1
print(n, time.time()-t, sorted(hist.items()))
