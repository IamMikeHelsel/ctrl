import time, numpy as np
from core import *
from ssclass import g_K
rng = np.random.default_rng(0)
for k in range(6):
    K, Y, err = random_pair(rng)
    t0=time.time(); out = g_K(K, Y, return_all=True); t1=time.time()
    print(k, out['lo'], out['hi'], 'it', out['it'], 'atoms', len(out['nu_w']), np.round(out['nu_w'],3), f"{t1-t0:.1f}s", flush=True)
