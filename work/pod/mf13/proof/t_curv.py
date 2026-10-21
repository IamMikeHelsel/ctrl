"""Second-order behaviour of N at n=6 maximisers: c(dir) = (1 - N(pair + e*dir)) / e^2 for random tangent directions
(perturb both K and Y, renormalise), directions orthogonal to the O(6)-orbit. Compare full-rank common-T maximiser vs rank-4 one."""
import warnings, sys; warnings.filterwarnings('ignore')
import numpy as np
import core
from core import skew_of
from staticN import N_of
rng = np.random.default_rng(7)
def pair_of(fn):
    A = np.load(fn); u, s, vt = np.linalg.svd(core.BK(A)); K = skew_of(vt[0], 6); Y = skew_of(u[:, 0], 6)
    return K / np.linalg.norm(K), Y / np.linalg.norm(Y)
def orbit_basis(K, Y):
    B = []
    for E in core.bases(6)[1]:
        B.append(np.concatenate([(E @ K - K @ E).ravel(), (E @ Y - Y @ E).ravel()]))
    B.append(np.concatenate([K.ravel(), 0 * Y.ravel()])); B.append(np.concatenate([0 * K.ravel(), Y.ravel()]))
    q, r = np.linalg.qr(np.array(B).T); return q[:, np.abs(np.diag(r)) > 1e-10]
for fn in sys.argv[1:]:
    K, Y = pair_of(fn); N0 = N_of(Y @ K); Qo = orbit_basis(K, Y)
    cs = []
    for t in range(40):
        d = np.concatenate([skew_of(rng.standard_normal(15), 6).ravel(), skew_of(rng.standard_normal(15), 6).ravel()])
        d -= Qo @ (Qo.T @ d); d /= np.linalg.norm(d)
        e = 1e-2
        Ke = K + e * d[:36].reshape(6, 6); Ye = Y + e * d[36:].reshape(6, 6)
        Ke /= np.linalg.norm(Ke); Ye /= np.linalg.norm(Ye)
        cs.append((N0 - N_of(Ye @ Ke)) / e ** 2)
    cs = np.sort(cs)
    print(f"{fn.split('/')[-1]}: N0={N0:.9f}  orbit dim={Qo.shape[1]}  curvature c: min={cs[0]:.4f} q10={cs[4]:.4f} median={np.median(cs):.4f} max={cs[-1]:.4f}", flush=True)
