import numpy as np
from scipy.stats import ortho_group
rng = np.random.default_rng(3)
for t in range(3):
    A = rng.standard_normal((6,6))
    Q = ortho_group.rvs(6, random_state=rng)
    w = rng.uniform(0.2,1,3)
    K0 = np.zeros((6,6)); 
    for i in range(3): K0[2*i,2*i+1]=w[i]; K0[2*i+1,2*i]=-w[i]
    K = Q@K0@Q.T
    th = rng.uniform(0,2*np.pi,3); T0 = np.zeros((6,6))
    for i in range(3): T0[2*i:2*i+2,2*i:2*i+2] = [[np.cos(th[i]),np.sin(th[i])],[np.sin(th[i]),-np.cos(th[i])]]
    T = Q@T0@Q.T
    Y = A@K+K@A.T
    Xv = K@T
    LHS = np.sum((A@Xv+Xv@A.T)**2)
    Yc = 0.5*(Y+T@Y@T)
    comm = T@A.T-A.T@T
    RHS = np.sum(Y*Y) + 4*np.trace(Yc@K@A.T) + np.sum((K@comm)**2)
    print("sym:", np.linalg.norm(Xv-Xv.T), " |L Xv|^2 =", LHS, " formula =", RHS)
