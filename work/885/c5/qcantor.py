# Erdos 885 / C5 certificate numerics (see lean/Research/Erdos885C5Chabauty.lean). Run from this dir.
from fractions import Fraction as Fr
from cantor import C5
class FQ:
    def norm(s,a):
        a=[Fr(c) for c in a]
        while a and a[-1]==0: a.pop()
        return a
    def add(s,a,b):
        n=max(len(a),len(b)); return s.norm([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)])
    def neg(s,a): return s.norm([-c for c in a])
    def sub(s,a,b): return s.add(a,s.neg(b))
    def mul(s,a,b):
        if not a or not b: return []
        r=[Fr(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): r[i+j]+=x*y
        return s.norm(r)
    def inv(s,c): return 1/Fr(c)
    def divmod(s,a,b):
        a=s.norm(a[:]); b=s.norm(b); q=[Fr(0)]*max(1,len(a)-len(b)+1)
        while len(a)>=len(b) and a:
            c=a[-1]/b[-1]; d=len(a)-len(b); q[d]=c
            a=s.sub(a,[0]*d+[c*x for x in b])
        return s.norm(q),a
    def monic(s,a): return s.norm([c/a[-1] for c in a]) if a else a
    def xgcd(s,a,b):
        r0,r1=s.norm(a),s.norm(b); u0,u1=[Fr(1)],[]; v0,v1=[],[Fr(1)]
        while r1:
            q,r=s.divmod(r0,r1)
            r0,r1=r1,r; u0,u1=u1,s.sub(u0,s.mul(q,u1)); v0,v1=v1,s.sub(v0,s.mul(q,v1))
        l=r0[-1]; return [c/l for c in r0],[c/l for c in u0],[c/l for c in v0]
