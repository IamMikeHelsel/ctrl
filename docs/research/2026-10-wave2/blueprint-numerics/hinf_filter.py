import numpy as np
rng=np.random.default_rng(3)
inv=np.linalg.inv
def lmi(A_,B_,C_,D_,X,g):
    top=np.hstack([A_.T@X@A_-X+C_.T@C_, A_.T@X@B_+C_.T@D_])
    bot=np.hstack([B_.T@X@A_+D_.T@C_, B_.T@X@B_+D_.T@D_-g*g*np.eye(B_.shape[1])])
    Mm=np.vstack([top,bot]); return np.max(np.linalg.eigvalsh((Mm+Mm.T)/2))
res={'post':[], 'prio':[], 'feas':0}
for trial in range(400):
    n=rng.integers(1,4); r=rng.integers(1,3); p=rng.integers(1,3); q=rng.integers(1,3)
    A=rng.normal(size=(n,n))*0.6; G=rng.normal(size=(n,r)); C=rng.normal(size=(p,n)); L=rng.normal(size=(q,n))
    g=rng.uniform(1.5,6)
    P=np.eye(n)*1.0; ok=True
    for it in range(3000):
        F=inv(P)+C.T@C-L.T@L/g**2
        if np.min(np.linalg.eigvalsh((F+F.T)/2))<=1e-9: ok=False;break
        Pn=A@inv(F)@A.T+G@G.T
        if np.linalg.norm(Pn-P)<1e-12: P=Pn;break
        P=Pn
    if not ok or np.linalg.norm(Pn-P)>1e-8: continue
    F=inv(P)+C.T@C-L.T@L/g**2
    if np.min(np.linalg.eigvalsh(F))<=1e-9 or np.min(np.linalg.eigvalsh(P))<=1e-9: continue
    res['feas']+=1
    Kf=P@C.T@inv(np.eye(p)+C@P@C.T); K=A@Kf
    AK=A-K@C; BK=np.hstack([G,-K]); X=g*g*inv(P)
    # a posteriori output: L(x - xhat_{k|k}) = L(I-Kf C) e - L Kf v
    Ce=L@(np.eye(n)-Kf@C); De=np.hstack([np.zeros((q,r)),-L@Kf])
    res['post'].append(lmi(AK,BK,Ce,De,X,g))
    # a priori output: L e
    res['prio'].append(lmi(AK,BK,L,np.zeros((q,r+p)),X,g))
print("feasible stationary cases",res['feas'])
print("a posteriori: max eig of BRL block with X=g^2 P^-1:",max(res['post']))
print("a priori:     max eig (fraction >1e-9):",max(res['prio']), np.mean(np.array(res['prio'])>1e-9))
# check strictness of M for the stationary a-posteriori certificate
rng=np.random.default_rng(3); mins=[]
for trial in range(400):
    n=rng.integers(1,4); r=rng.integers(1,3); p=rng.integers(1,3); q=rng.integers(1,3)
    A=rng.normal(size=(n,n))*0.6; G=rng.normal(size=(n,r)); C=rng.normal(size=(p,n)); L=rng.normal(size=(q,n)); g=rng.uniform(1.5,6)
    P=np.eye(n); ok=True
    for it in range(3000):
        F=inv(P)+C.T@C-L.T@L/g**2
        if np.min(np.linalg.eigvalsh((F+F.T)/2))<=1e-9: ok=False;break
        Pn=A@inv(F)@A.T+G@G.T
        if np.linalg.norm(Pn-P)<1e-12: P=Pn;break
        P=Pn
    if not ok or np.linalg.norm(Pn-P)>1e-8: continue
    Kf=P@C.T@inv(np.eye(p)+C@P@C.T); K=A@Kf; BK=np.hstack([G,-K]); X=g*g*inv(P)
    De=np.hstack([np.zeros((q,r)),-L@Kf]); M=g*g*np.eye(r+p)-BK.T@X@BK-De.T@De
    mins.append(np.min(np.linalg.eigvalsh((M+M.T)/2))/g**2)
print("stationary: min eig(M)/g^2 over cases:",min(mins))
