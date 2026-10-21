import json, glob, sys
import numpy as np
from evalf import *
np.set_printoptions(precision=4, suppress=False, linewidth=170)
fn = sys.argv[1]
h = float(sys.argv[2]) if len(sys.argv) > 2 else 2e-3
d = json.load(open(fn)); x0 = np.array(d['x'])
def F(x):
    w = abc_from_uv(x[0], x[1]); K = make_K(*w)
    Y, err = Y_from_x(K, x[2:])
    return f_of_pair(K, Y, tol=1e-13)['f']
n = len(x0)
f0 = F(x0)
print("f0-1 =", f0 - 1)
# gradient & hessian by central differences
g = np.zeros(n); Hs = np.zeros((n, n))
fp = np.zeros(n); fm = np.zeros(n)
for i in range(n):
    e = np.zeros(n); e[i] = h
    fp[i] = F(x0 + e); fm[i] = F(x0 - e)
    g[i] = (fp[i] - fm[i]) / (2 * h); Hs[i, i] = (fp[i] - 2 * f0 + fm[i]) / h**2
for i in range(n):
    for j in range(i + 1, n):
        ei = np.zeros(n); ei[i] = h; ej = np.zeros(n); ej[j] = h
        v = (F(x0 + ei + ej) - F(x0 + ei - ej) - F(x0 - ei + ej) + F(x0 - ei - ej)) / (4 * h * h)
        Hs[i, j] = Hs[j, i] = v
print("|grad|", np.linalg.norm(g))
ev, V = np.linalg.eigh(Hs)
print("Hessian eigenvalues:", ev)
np.save(fn.replace('.json', '.hess.npy'), Hs)
