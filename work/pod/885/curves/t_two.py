import sys
from deform2 import solve, Z0, pari, polys, INC
from obstr import R, C
msq=pari("msq"); X=pari("x")
b11=msq(R[1]+C[1]); b12=msq(R[1]+C[2])
print("b11",pari.factor(b11),"b12",pari.factor(b12))
w1=b11/pari.pollead(b11); w2=b12/pari.pollead(b12)
for t1,t2 in [("0","1"),("1","0"),("1","1"),("1/3","-2/7")]:
    C1=C[1]+pari(t1)*w1**2; C2=C[2]+pari(t2)*w2**2
    f={("C",1,k):pari.polcoef(C1,k) for k in range(5)}
    f.update({("C",2,k):pari.polcoef(C2,k) for k in range(5)})
    f.update({("a",1,k):pari.polcoef(msq(R[1]),k) for k in range(3)})
    try:
        z,res,it=solve(f,its=40)
        print(t1,t2,"res",pari.precision(res,4),"its",it)
    except Exception as e: print(t1,t2,"fail",str(e)[:60])
