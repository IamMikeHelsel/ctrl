# Erdos 885 / C5 certificate numerics (see lean/Research/Erdos885C5Chabauty.lean). Run from this dir.
from fractions import Fraction as F
from math import isqrt
C=[0,123200,35704,2796,89,1]
def fmod(a1,a0):
    # reduce f mod x^2+a1 x+a0, return (r1,r0)
    coeffs=[F(c) for c in C]
    for d in range(5,1,-1):
        c=coeffs[d]; coeffs[d]=0
        coeffs[d-1]-=c*a1; coeffs[d-2]-=c*a0
    return coeffs[1],coeffs[0]
def issq(q):
    if q<0: return None
    n,d=q.numerator,q.denominator
    a,b=isqrt(n),isqrt(d)
    return F(a,b) if a*a==n and b*b==d else None
found=[]
N=400
for a1 in range(-N,N+1):
    for a0 in range(-N,N+1):
        disc=a1*a1-4*a0
        if disc>=0 and issq(F(disc)) is not None: continue  # skip split a (rational x)
        r1,r0=fmod(a1,a0)
        if r1==0:
            v=issq(r0)
            if v is not None: found.append((a1,a0,0,v)); print("const",a1,a0,v,flush=True)
            continue
        A=F(disc); B=2*r1*a1-4*r0; Cc=r1*r1
        D=B*B-4*A*Cc
        s=issq(D)
        if s is None: continue
        for t in [(-B+s)/(2*A),(-B-s)/(2*A)]:
            u=issq(t)
            if u is not None and u!=0:
                v=(r1+u*u*a1)/(2*u)
                found.append((a1,a0,u,v)); print(a1,a0,u,v,flush=True)
print(len(found))
