import numpy as np, time
from n6 import *
from inner import *
from bl import inner_min
rng = np.random.default_rng(3)
ts = []
for t in range(8):
    K, Y, err = random_pair(rng)
    A0, Ar, resid, rank = affine_family(K, Y)
    t0 = time.time(); f, z = inner_f(A0, Ar); t1 = time.time() - t0
    t0 = time.time(); f2 = inner_min(A0, Ar); t2 = time.time() - t0
    A = A0 + np.tensordot(z, Ar, axes=(0, 0))
    s, k = norms(A)
    print(f"f={f:.9f} cvxpy={f2:.9f} t_direct={t1*1e3:.1f}ms t_cvxpy={t2*1e3:.0f}ms  sym(A_opt)={s:.9f} skew={k:.4f}  f(A0)={norms(A0)[0]:.4f}")
