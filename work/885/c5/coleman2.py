# Erdos 885 / C5 certificate numerics (see lean/Research/Erdos885C5Chabauty.lean). Run from this dir.
import sys
from fractions import Fraction as Fr
from cantor import C5, jmul
from qcantor import FQ
p=int(sys.argv[1]); mult=int(sys.argv[2]); disk=sys.argv[3]  # disk: 'W0' or 'inf'
K=int(sys.argv[4]) if len(sys.argv)>4 else 41
F=FQ()
D=(F.norm([32,8,1]),F.norm([272,136]))
E=jmul(F,mult,D)
def v(x):
    x=Fr(x)
    if x==0: return 10**9
    n,d=x.numerator,x.denominator; k=0
    while n%p==0: n//=p;k+=1
    while d%p==0: d//=p;k-=1
    return k
print("a_E vals",[v(c) for c in E[0]],"b_E vals",[v(c) for c in E[1]], "deg a", len(E[0])-1)
def smul(a,b):
    r=[Fr(0)]*K
    for i,x in enumerate(a):
        if x==0: continue
        for j in range(K-i): r[i+j]+=x*b[j]
    return r
def sinv(a):
    r=[Fr(0)]*K; r[0]=1/a[0]
    for n in range(1,K): r[n]=-sum(a[k]*r[n-k] for k in range(1,n+1))/a[0]
    return r
def deriv(a): return [(i+1)*a[i+1] for i in range(K-1)]+[Fr(0)]
if disk=='W0':
    # uniformizer s=y; x = y^2 / q(x), q(x)=123200+35704x+2796x^2+89x^3+x^4
    x=[Fr(0)]*K
    for it in range(K):
        xs=[x]; 
        for _ in range(3): xs.append(smul(xs[-1],x))
        q=[Fr(0)]*K; q[0]=Fr(123200)
        for i in range(K): q[i]+=35704*xs[0][i]+2796*xs[1][i]+89*xs[2][i]+xs[3][i]
        y2=[Fr(0)]*K; y2[2]=Fr(1)
        x=smul(y2,sinv(q))
    xp=deriv(x)
    # dx/y = x'(s) ds / s
    om0=xp[1:]+[Fr(0)]
    om1=smul(x,om0)
    def param(X2,X,bX,qmul,qinv): return bX  # s = y = b(X)
else:
    w=[Fr(0)]*K
    for it in range(K):
        w2=smul(w,w); w3=smul(w2,w); w4=smul(w3,w)
        den=[Fr(1) if i==0 else Fr(0) for i in range(K)]
        for i in range(K): den[i]+=89*w[i]+2796*w2[i]+35704*w3[i]+123200*w4[i]
        t2=[Fr(0)]*K; t2[2]=Fr(1); w=smul(t2,sinv(den))
    wp=deriv(w)
    om0=[-c for c in smul([0,1]+[0]*(K-2),wp)]
    W=w[2:]+[Fr(0)]*2
    om1=[-c for c in smul(wp[1:]+[Fr(0)],sinv(W))]
    def param(X2,X,bX,qmul,qinv): return qmul(X2,qinv(bX))
print("om0/ds",[str(c) for c in om0[:5]]); print("om1/ds",[str(c) for c in om1[:5]])
I0=[Fr(0)]+[om0[k]/(k+1) for k in range(K-1)]
I1=[Fr(0)]+[om1[k]/(k+1) for k in range(K-1)]
aE,bE=E; e0,e1=aE[0],aE[1]
def qmul(u,w_):
    c0=u[0]*w_[0]; c1=u[0]*w_[1]+u[1]*w_[0]; c2=u[1]*w_[1]
    return (c0-c2*e0, c1-c2*e1)
def qinv(u):
    conj=(u[0]-e1*u[1], -u[1]); n=qmul(u,conj); return (conj[0]/n[0],conj[1]/n[0])
tr=lambda u: 2*u[0]-e1*u[1]
nm=lambda u: qmul(u,(u[0]-e1*u[1],-u[1]))[0]
X=(Fr(0),Fr(1)); X2=qmul(X,X)
bX=(bE[0] if bE else Fr(0), bE[1] if len(bE)>1 else Fr(0))
s=param(X2,X,bX,qmul,qinv)
print("param: v(trace), v(norm):", v(tr(s)), v(nm(s)))
def ev(I):
    acc=(Fr(0),Fr(0)); pw=(Fr(1),Fr(0))
    for k in range(K):
        if I[k]!=0: acc=(acc[0]+I[k]*pw[0],acc[1]+I[k]*pw[1])
        pw=qmul(pw,s)
    return tr(acc)
L0=ev(I0); L1=ev(I1)
def red(x,prec=6):
    x=Fr(x); k=v(x); u=x/Fr(p)**k; m=p**prec
    return k,(u.numerator*pow(u.denominator,-1,m))%m
print("L0=int dx/y", red(L0)); print("L1=int x dx/y", red(L1))
vmin=min(v(L0),v(L1)); al=L1/Fr(p)**vmin; be=-L0/Fr(p)**vmin
print("alpha",red(al,3),"beta",red(be,3), "ratio beta/alpha mod p^3:", red(be/al,3))
