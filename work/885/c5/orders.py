# Erdos 885 / C5 certificate numerics (see lean/Research/Erdos885C5Chabauty.lean). Run from this dir.
from cantor import *
from jac import Jcount, primes, BAD, fp, leg
from math import sqrt
res={}
for p in primes(200):
    if p in BAD: continue
    F=Fp(p)
    D=(F.norm([32,8,1]),F.norm([272,136]))
    T=(F.norm([0,1]),[])
    J=Jcount(p)[2]
    oD=order(F,D,J); oT=order(F,T,J)
    # check T in <D>?
    R=ZERO; inD=None
    for n in range(oD):
        if R==T: inD=n
        R=cantor(F,R,D)
    res[p]=(J,oD,inD)
    print(p,J,oD,J%oD==0,"T=nD:",inD)
