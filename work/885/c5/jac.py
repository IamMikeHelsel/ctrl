# Erdos 885 / C5 certificate numerics (see lean/Research/Erdos885C5Chabauty.lean). Run from this dir.
from math import gcd
from functools import reduce
C=[0,123200,35704,2796,89,1]  # f coefficients low->high
BAD={2,3,5,7,11,176844303367}
def primes(n):
    s=[1]*(n+1);s[0]=s[1]=0
    for i in range(2,n+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=0
    return [i for i in range(n+1) if s[i]]
def fp(x,p): 
    r=0
    for c in reversed(C): r=(r*x+c)%p
    return r
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def N1(p): return 1+sum(1+leg(fp(x,p),p) for x in range(p))
# F_{p^2}: find nonresidue d, elements a+b*sqrt(d)
def N2(p):
    d=next(d for d in range(2,p) if leg(d,p)==-1)
    def mul(u,v): return ((u[0]*v[0]+d*u[1]*v[1])%p,(u[0]*v[1]+u[1]*v[0])%p)
    def pw(u,e):
        r=(1,0)
        while e:
            if e&1: r=mul(r,u)
            u=mul(u,u); e>>=1
        return r
    q=p*p; cnt=1
    for a in range(p):
        for b in range(p):
            x=(a,b); r=(0,0)
            for c in reversed(C): r=mul(r,x); r=((r[0]+c)%p,r[1])
            if r==(0,0): cnt+=1
            else:
                t=pw(r,(q-1)//2)
                cnt+= 2 if t==(1,0) else 0
    return cnt
def Jcount(p):
    n1,n2=N1(p),N2(p)
    a1=n1-p-1          # N1 = p+1 - s1? convention: N1 = p+1 + a1 where L(T)=1 - ... ; use standard
    # L(T)=1+c1 T+c2 T^2+p c1 T^3+p^2 T^4, N1=p+1+c1? Let s1 = p+1-N1 (sum of alphas), s2 = p^2+1-N2
    s1=p+1-n1; s2=p*p+1-n2
    # e1 = s1, e2 = (s1^2 - s2)/2
    e1=s1; e2=(s1*s1-s2)//2
    # L(T)=1 - e1 T + e2 T^2 - p e1 T^3 + p^2 T^4 ; #J = L(1)
    return n1,n2,1-e1+e2-p*e1+p*p, (e1,e2)
if __name__=="__main__":
    res={}
    for p in primes(110):
        if p in BAD: continue
        n1,n2,J,e=Jcount(p); res[p]=J
        # factor J
        def fac(n):
            out={};k=2
            while k*k<=n:
                while n%k==0: out[k]=out.get(k,0)+1; n//=k
                k+=1
            if n>1: out[n]=out.get(n,0)+1
            return out
        print(p,n1,n2,J,fac(J),e)
    print("gcd",reduce(gcd,res.values()))
