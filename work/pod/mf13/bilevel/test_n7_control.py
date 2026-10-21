import numpy as np, time
from bl import *

A7 = np.array([
 [0,0,0,0,0,0,0],
 [0,0,0,0,0,0,0],
 [6,-5,-13,0,0,0,0],
 [-14,-18,0,0,0,0,0],
 [12,-12,11,0,0,0,0],
 [0,0,0,-6,0,-14,0],
 [0,0,0,6,-18,0,0]], float)
s, k = norms(A7)
print("paper A: s^2=%.6f  k^2=%.6f (expect 1195.593985, 1196.025224)" % (s**2, k**2))
s2, k2 = full_op_matrix_norms(A7)
print("full kron check: s^2=%.6f k^2=%.6f" % (s2**2, k2**2))

# skew top pair
sig, K, Y, sv = skew_top_pair(A7)
print("skew top sv", sv[:6], " sigma=", sig)
print("K sv:", np.linalg.svd(K, compute_uv=False)); print("Y sv:", np.linalg.svd(Y, compute_uv=False))
A = A7 / sig
# check pair equations
print("pair resid:", np.linalg.norm(A@K+K@A.T-Y), np.linalg.norm(A.T@Y+Y@A-K), "norms", np.linalg.norm(K), np.linalg.norm(Y))
A0, Ar, resid, rank, s_ = affine_family(K, Y, return_info=True)
print("affine family: resid", resid, "rank", rank, "nullity", len(Ar), "sv tail", s_[-12:])
# is A in the family? 
print("sym ratio of A:", s/sig, " (f upper bound)", )
t0 = time.time()
f, z = inner_min(A0, Ar, return_z=True)
print("INNER MIN f =", f, " time", time.time()-t0, " gap 1-f=", 1-f)
Aopt = A0 + np.tensordot(z, Ar, axes=(0,0))
sO, kO = norms(Aopt)
print("A_opt: sym norm %.10f skew norm %.10f  ratio sym/skew %.10f" % (sO, kO, sO/kO))
print("pair resid opt:", np.linalg.norm(Aopt@K+K@Aopt.T-Y), np.linalg.norm(Aopt.T@Y+Y@Aopt-K))
print("paper ratio sqrt(s2/k2) =", s/k)
