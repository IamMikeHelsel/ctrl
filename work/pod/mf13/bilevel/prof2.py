import numpy as np, time
from n6 import *
from inner import *
from barrier import *
rng = np.random.default_rng(3)
for _ in range(5):
    K, Y, err = random_pair(rng)
    A0, Ar, resid, rank = affine_family(K, Y)
    B0 = BS(A0); Br = np.array([BS(A) for A in Ar])
    t0 = time.time(); t, z = sdp_sigma_min(B0, Br, tol=1e-9); t1 = time.time() - t0
    t0 = time.time(); s, z2, tt, nit = barrier_min_sigma(B0, Br, tol=1e-9); t2 = time.time() - t0
    print(f"clarabel {t:.10f} ({t1*1e3:.0f}ms)   barrier {s:.10f} t={tt:.10f} nit={nit} ({t2*1e3:.0f}ms)")
