import sys, json
import numpy as np
fn = sys.argv[1]; n = int(sys.argv[2])
sys.argv = ['x', str(n), '1', '0.02', '1']
import track_a_gen as T
from bl import *
d = json.load(open(fn)); x = np.array(d['x'])
K, Y, err = T.build(x)
print("proj err", err)
A0, Ar, resid, rank, s = affine_family(K, Y, return_info=True)
print("resid", resid, "rank", rank, "nullity", len(Ar), "sv around cut:", s[rank-3:rank+1], s[-14:])
sK = np.linalg.svd(K, compute_uv=False); sY = np.linalg.svd(Y, compute_uv=False)
print("sv K", sK, "sv Y", sY)
B0 = BS(A0); Br = np.array([BS(a) for a in Ar])
from barrier import barrier_min_sigma
fv, z, t, nit = barrier_min_sigma(B0, Br, tol=1e-13)
A = A0 + np.tensordot(z, Ar, axes=(0, 0))
print("f =", fv, "  |z|", np.linalg.norm(z))
sA, kA = norms(A); print("s(A)", sA, "k(A)", kA)
print("pair residuals: ", np.linalg.norm(A @ K + K @ A.T - Y), np.linalg.norm(A.T @ Y + Y @ A - K))
print("skew sv top:", np.linalg.svd(BK(A), compute_uv=False)[:3])
