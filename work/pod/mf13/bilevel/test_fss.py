import numpy as np, time, json, glob
from fss import *
rng = np.random.default_rng(11)
print("random pairs: f vs f_ss (R-type anticommuting same-square both sides)")
for t in range(6):
    K, Y, err = random_pair(rng)
    out = f_of_pair(K, Y)
    t0 = time.time()
    up, lo, z = f_ss(K, Y)
    print(f"f={out['f']:.6f}  f_ss in [{lo:.6f},{up:.6f}]  ({time.time()-t0:.1f}s)")
print("ridge points:")
for fn in sorted(glob.glob('runs/A_*.best.json')):
    d = json.load(open(fn)); x = np.array(d['x'])
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    out = f_of_pair(K, Y)
    up, lo, z = f_ss(K, Y)
    print(fn, f"f={out['f']:.8f}  f_ss in [{lo:.8f},{up:.8f}]")
