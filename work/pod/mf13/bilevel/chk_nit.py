import json, glob, numpy as np
from evalf import *
for fn in sorted(glob.glob('runs/A_*.best.json')):
    d = json.load(open(fn)); x = np.array(d['x'])
    w = abc_from_uv(x[0], x[1]); K = make_K(*w); Y, err = Y_from_x(K, x[2:])
    for tol in (1e-9, 1e-12):
        out = f_of_pair(K, Y, tol=tol)
        print(fn.split('/')[-1], tol, "f-1 =", out['f']-1, "nit", out['nit'])
