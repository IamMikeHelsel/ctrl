import numpy as np, time
from n6 import *
from inner import *
rng = np.random.default_rng(3)
K, Y, err = random_pair(rng)
A0, Ar, resid, rank = affine_family(K, Y)
B0=BS(A0); Br=[BS(A) for A in Ar]
for tol in (1e-6,1e-8,1e-10):
    t0=time.time(); t,z,sol=sdp_sigma_min(B0,Br,tol=tol,return_all=True); print(tol,t,time.time()-t0, sol.iterations, sol.solve_time)
import cProfile
cProfile.run('sdp_sigma_min(B0,Br,tol=1e-8)',sort='cumtime')
