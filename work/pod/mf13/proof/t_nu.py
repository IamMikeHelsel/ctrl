import warnings; warnings.filterwarnings('ignore')
import numpy as np
from core import *
from ssclass import g_K
np.set_printoptions(precision=3, suppress=True, linewidth=150)
rng = np.random.default_rng(0)
for k in range(4):
    K, Y, err = random_pair(rng)
    if k not in (1,2,3): continue
    out = g_K(K, Y, return_all=True)
    th = out['nu_th']; w = out['nu_w']
    # canonicalise theta mod the global pi shift: make th1 in [0,pi)
    sh = np.where(np.mod(th[:,0],2*np.pi) >= np.pi, np.pi, 0)
    thc = np.mod(th - sh[:,None], 2*np.pi)
    order = np.argsort(thc[:,0])
    print(f"pair {k} g={out['hi']:.6f}")
    for i in order:
        if w[i] > 2e-3: print("   ", thc[i], f"{w[i]:.4f}")
    # check: differences th2-th1, th3-th1, sums
    print("   th2-th1:", np.round(np.mod(thc[order,1]-thc[order,0],2*np.pi)[w[order]>2e-3],2))
    print("   th3-th1:", np.round(np.mod(thc[order,2]-thc[order,0],2*np.pi)[w[order]>2e-3],2))
