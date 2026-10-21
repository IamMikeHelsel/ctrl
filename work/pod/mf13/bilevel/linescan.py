import json, sys
import numpy as np
from evalf import *
fn = sys.argv[1]
d = json.load(open(fn)); x0 = np.array(d['x'])
Hs = np.load(fn.replace('.json', '.hess.npy'))
def F(x):
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    return f_of_pair(K, Y, tol=1e-13)['f']
ev, V = np.linalg.eigh(Hs)
f0 = F(x0); print("f0-1", f0 - 1)
for k in list(range(0, 8)) + [14, 15, 16]:
    row = []
    for t in (-1e-1, -1e-2, -1e-3, 1e-3, 1e-2, 1e-1):
        row.append(F(x0 + t * V[:, k]) - 1)
    print(f"eig {ev[k]: .2e}:", " ".join(f"{r: .2e}" for r in row), flush=True)
