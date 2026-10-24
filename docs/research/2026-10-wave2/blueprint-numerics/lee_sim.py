import numpy as np
def hat(v): return np.array([[0,-v[2],v[1]],[v[2],0,-v[0]],[-v[1],v[0],0]])
def vee(S): return np.array([S[2,1],S[0,2],S[1,0]])
def expm(S):
    out=np.eye(3); term=np.eye(3)
    for k in range(1,30): term=term@S/k; out=out+term
    return out
J=np.diag([1.,2.,3.]); lm,lM=1.,3.; kR,kW,c,dl,psi=8.,4.,0.1,1.0,1.9
WR=c*(kR-kW*dl/2); WW=kW-c*lM-c*kW/(2*dl); UR=kR/(2-psi)+c/2; UW=lM/2+c*lM**2/2
LR=kR/2-c/2; LW=lm/2-c*lM**2/2; beta=min(WR/UR,WW/UW)
print("WR,WW,LR,LW,beta",WR,WW,LR,LW,beta)
Wd=lambda t: np.array([np.sin(t),0.5*np.cos(2*t),0.3])
Wdd=lambda t: np.array([np.cos(t),-np.sin(2*t),0.])
rng=np.random.default_rng(2)
worst=-1
for trial in range(20):
    # initial condition with Psi(0) small enough so V0(0)<=kR psi
    ax=rng.normal(size=3); ax/=np.linalg.norm(ax); th=rng.uniform(0,2.3)
    R=expm(th*hat(ax)); Rd=np.eye(3); W=rng.normal(size=3)*0.5
    def errs(R,Rd,W,t):
        E=Rd.T@R; Psi=0.5*np.trace(np.eye(3)-E); eR=0.5*vee(E-E.T); eW=W-R.T@Rd@Wd(t); return Psi,eR,eW
    Psi,eR,eW=errs(R,Rd,W,0)
    V00=0.5*eW@J@eW+kR*Psi
    if V00>kR*psi: continue
    V=lambda Psi,eR,eW: 0.5*eW@J@eW+kR*Psi+c*eR@J@eW
    Vinit=V(Psi,eR,eW); dt=1e-3; t=0
    for k in range(8000):
        Psi,eR,eW=errs(R,Rd,W,t)
        E=R.T@Rd
        M=-kR*eR-kW*eW+np.cross(W,J@W)-J@(hat(W)@E@Wd(t)-E@Wdd(t))
        Wdot=np.linalg.solve(J,M-np.cross(W,J@W))
        R=R@expm(dt*hat(W)); Rd=Rd@expm(dt*hat(Wd(t))); W=W+dt*Wdot; t+=dt
        Psi,eR,eW=errs(R,Rd,W,t)
        assert Psi<=psi+1e-6
        ratio=V(Psi,eR,eW)/(np.exp(-beta*t)*Vinit)
        worst=max(worst,ratio)
print("max V(t)/(exp(-beta t)V(0)) over sims (<=1 expected, Euler error):",worst)
