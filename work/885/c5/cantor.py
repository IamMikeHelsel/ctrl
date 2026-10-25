# Erdos 885 / C5 certificate numerics (see lean/Research/Erdos885C5Chabauty.lean). Run from this dir.
# Cantor's algorithm for y^2 = f(x), deg f = 5, over F_p. Polys: lists low->high, normalized.
C5=[0,123200,35704,2796,89,1]
class Fp:
    def __init__(s,p): s.p=p
    def norm(s,a):
        a=[c%s.p for c in a]
        while a and a[-1]==0: a.pop()
        return a
    def add(s,a,b):
        n=max(len(a),len(b)); return s.norm([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)])
    def neg(s,a): return s.norm([-c for c in a])
    def sub(s,a,b): return s.add(a,s.neg(b))
    def mul(s,a,b):
        if not a or not b: return []
        r=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): r[i+j]+=x*y
        return s.norm(r)
    def inv(s,c): return pow(c%s.p,s.p-2,s.p)
    def divmod(s,a,b):
        a=s.norm(a[:]); b=s.norm(b); q=[0]*max(1,len(a)-len(b)+1)
        il=s.inv(b[-1])
        while len(a)>=len(b) and a:
            c=a[-1]*il%s.p; d=len(a)-len(b); q[d]=c
            a=s.sub(a,[0]*d+[c*x for x in b])
        return s.norm(q),a
    def monic(s,a):
        if not a: return a
        il=s.inv(a[-1]); return s.norm([c*il for c in a])
    def xgcd(s,a,b):
        # returns g,u,v with u a + v b = g monic
        r0,r1=s.norm(a),s.norm(b); u0,u1=[1],[]; v0,v1=[],[1]
        while r1:
            q,r=s.divmod(r0,r1)
            r0,r1=r1,r; u0,u1=u1,s.sub(u0,s.mul(q,u1)); v0,v1=v1,s.sub(v0,s.mul(q,v1))
        il=s.inv(r0[-1]); return [c*il%s.p for c in r0],s.norm([c*il for c in u0]),s.norm([c*il for c in v0])
def cantor(F,D1,D2,f=C5):
    a1,b1=D1;a2,b2=D2
    d0,e1,e2=F.xgcd(a1,a2)
    d,c1,c2=F.xgcd(d0,F.add(b1,b2))
    s1=F.mul(c1,e1);s2=F.mul(c1,e2);s3=c2
    a=F.divmod(F.mul(a1,a2),F.mul(d,d))[0]
    num=F.add(F.add(F.mul(F.mul(s1,a1),b2),F.mul(F.mul(s2,a2),b1)),F.mul(s3,F.add(F.mul(b1,b2),f)))
    b=F.divmod(F.divmod(num,d)[0],a)[1]
    while len(a)-1>2:
        a=F.monic(F.divmod(F.sub(f,F.mul(b,b)),a)[0])
        b=F.divmod(F.neg(b),a)[1]
    return (F.monic(a),b)
ZERO=([1],[])
def jneg(F,D): return (D[0],F.neg(D[1]))
def jmul(F,n,D):
    if n<0: return jmul(F,-n,jneg(F,D))
    R=ZERO; Q=D
    while n:
        if n&1: R=cantor(F,R,Q)
        Q=cantor(F,Q,Q); n>>=1
    return R
def order(F,D,bound):
    R=ZERO
    for n in range(1,bound+1):
        R=cantor(F,R,D)
        if R==ZERO: return n
    return None
