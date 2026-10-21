import sys, time
sys.argv = ['x', sys.argv[1], '1', '0.02', '1']
import numpy as np
import track_a_gen as T
rng = np.random.default_rng(0)
for t in range(4):
    x = rng.standard_normal(2 + T.m)
    t0 = time.time(); K, Y, err = T.build(x); t1 = time.time() - t0
    t0 = time.time(); o, info = T.objective(x, full=True); t2 = time.time() - t0
    print("proj err", err, "time proj", t1, " obj time", t2, " f", None if info is None else (info['f'], info['nullity']))
