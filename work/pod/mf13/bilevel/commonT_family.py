"""Construct compatible pairs inside the common-T locus: T=diag(I3,-I3), K=[[0,-C^T],[C,0]], Y=[[0,-D^T],[D,0]];
solve m0=m1=m2=0 for D (GN in the 9 entries of D) and compute f(K,Y) (should be exactly 1)."""
import sys
import numpy as np
from evalf import *
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)

def KY(C, D):
    K = np.zeros((6, 6)); K[:3, 3:] = -C.T; K[3:, :3] = C
    Y = np.zeros((6, 6)); Y[:3, 3:] = -D.T; Y[3:, :3] = D
    return K, Y

def mom(K, Y): return moments(K, Y)

res = []
for t in range(25):
    C = rng.standard_normal((3, 3)); C /= np.sqrt(2) * np.linalg.norm(C)      # |K|_F = 1
    d = rng.standard_normal(9)
    ok = False
    for it in range(60):
        K, Y = KY(C, d.reshape(3, 3))
        m = mom(K, Y)
        if np.linalg.norm(m) < 1e-14: ok = True; break
        J = np.array([(mom(*KY(C, (d + 1e-7 * e).reshape(3, 3))) - m) / 1e-7 for e in np.eye(9)]).T
        dd = np.linalg.lstsq(J, -m, rcond=1e-10)[0]
        n_ = np.linalg.norm(dd); dd *= min(1, 0.3 / n_)
        d = d + dd
    if not ok: continue
    K, Y = KY(C, d.reshape(3, 3))
    sK = np.linalg.svd(K, compute_uv=False)[::2]; sY = np.linalg.svd(Y, compute_uv=False)[::2]
    out = f_of_pair(K, Y, tol=1e-11)
    T = np.diag([1, 1, 1, -1, -1, -1.])
    res.append(out['f'])
    print(f"{t}: |m|<1e-14, sK={np.round(sK,3)} sY={np.round(sY,3)} nullity={out['nullity']} kept={out['kept_sv']:.1e} nit={out['nit']} f-1={out['f']-1:.2e}  anticomm: {np.linalg.norm(T@K+K@T):.0e} {np.linalg.norm(T@Y+Y@T):.0e}")
print("min f-1", min(res) - 1, "max f-1", max(res) - 1)
