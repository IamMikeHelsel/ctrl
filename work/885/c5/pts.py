# Erdos 885 / C5 certificate numerics (see lean/Research/Erdos885C5Chabauty.lean). Run from this dir.
from math import isqrt, gcd
def f(x): return x**5+89*x**4+2796*x**3+35704*x**2+123200*x
# rational points x=a/c^2, w=b/c^5: b^2 = a^5+89a^4c^2+2796a^3c^4+35704a^2c^6+123200ac^8
pts=[]
for c in range(1,200):
    c2=c*c
    for a in range(-200000,200001):
        if gcd(a,c)!=1: continue
        v=a**5+89*a**4*c2+2796*a**3*c2**2+35704*a**2*c2**3+123200*a*c2**4
        if v<0: continue
        r=isqrt(v)
        if r*r==v: pts.append((a,c,r))
    if c<5 or c%20==0: print(c,pts,flush=True)
print(pts)
