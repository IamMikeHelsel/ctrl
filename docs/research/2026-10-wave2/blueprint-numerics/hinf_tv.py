import numpy as np
rng=np.random.default_rng(5); inv=np.linalg.inv
worst=-1e9; cnt=0; minM=1e9
for trial in range(3000):
    n=rng.integers(1,4); r=rng.integers(1,4); p=rng.integers(1,3); q=rng.integers(1,3)
    A=rng.normal(size=(n,n)); G=rng.normal(size=(n,r)); C=rng.normal(size=(p,n)); L=rng.normal(size=(q,n))
    g=rng.uniform(0.5,5)
    Z=rng.normal(size=(n,n)); Y=Z@Z.T*rng.uniform(0,2)           # information matrix Y = P^-1 (PSD, maybe singular)
    if trial%4==0: Y=np.zeros((n,n))
    Pi=Y+C.T@C; F=Pi-L.T@L/g**2
    if np.min(np.linalg.eigvalsh(F))<=1e-6: continue
    Pp=A@inv(F)@A.T+G@G.T
    if np.min(np.linalg.eigvalsh(Pp))<=1e-8: continue
    Yp=inv(Pp); cnt+=1
    for _ in range(5):
        e=rng.normal(size=n); w=rng.normal(size=r); v=rng.normal(size=p)
        y=C@e+v; eps=e-inv(Pi)@C.T@y; ep=A@eps+G@w
        J=g*g*ep@Yp@ep + (L@eps)@(L@eps) - g*g*(w@w+v@v) - g*g*e@Y@e
        worst=max(worst,J/(1+e@e+w@w+v@v))
print("cases",cnt,"max normalized one-step J (should be <=0):",worst)
# stationary: smallest eig of M = g^2 I - BK^T X BK - De^T De
