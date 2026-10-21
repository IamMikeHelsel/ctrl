import numpy as np
from evalf import *
from gcert import *
rng = np.random.default_rng(5)
# 1. verify identity 2 tr(A M) = -(<Z1,Y>+<Z2,K>) for any A in family
K, Y, err = random_pair(rng)
A0, Ar, resid, rank = affine_family(K, Y)
Z1 = rng.standard_normal((6, 6)); Z1 -= Z1.T; Z2 = rng.standard_normal((6, 6)); Z2 -= Z2.T
M = Z1 @ K + Y @ Z2
z = rng.standard_normal(9)
A = A0 + np.tensordot(z, Ar, axes=(0, 0))
print("identity check:", 2 * np.trace(A @ M), -(np.sum(Z1 * Y) + np.sum(Z2 * K)))
# 2. g vs f on random pairs
for t in range(10):
    K, Y, err = random_pair(rng)
    out = f_of_pair(K, Y)
    g = g_cert(K, Y)
    print(f"f={out['f']:.6f}  g={g:.6f}   <K,Y>={np.sum(K*Y):.4f}")
