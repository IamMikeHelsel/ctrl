"""N(YK) on the common-T locus: K = [[0,BK],[-BK^T,0]], Y = [[0,BY],[-BY^T,0]] (T = diag(I3,-I3)), unit norms.
Upper bound 1 (YK = (YT)(TK)); lower bound nuclear norm = 2||BY BK^T||_*.  Which common-T pairs have N = 1?
Also: normal perturbations off the locus at maximisers: N(Y(e)K) - 1 vs e (second order?)."""
import warnings; warnings.filterwarnings('ignore')
import numpy as np
from core import *
from staticN import N_of
rng = np.random.default_rng(1)
import core
def ct(Bk, By):
    Z = np.zeros((3, 3))
    K = np.block([[Z, Bk], [-Bk.T, Z]]); Y = np.block([[Z, By], [-By.T, Z]])
    return K / np.linalg.norm(K), Y / np.linalg.norm(Y)
print("random common-T pairs:")
for t in range(0):
    K, Y = ct(rng.standard_normal((3, 3)), rng.standard_normal((3, 3)))
    print(f"  N={N_of(Y@K):.6f}  nuc={np.linalg.norm(Y@K,'nuc'):.6f}")
print("BY = O1 BK O2 (same singular values):")
for t in range(3):
    Bk = rng.standard_normal((3, 3)); O1 = np.linalg.qr(rng.standard_normal((3, 3)))[0]; O2 = np.linalg.qr(rng.standard_normal((3, 3)))[0]
    K, Y = ct(Bk, O1 @ Bk @ O2); print(f"  N={N_of(Y@K):.6f}  nuc={np.linalg.norm(Y@K,'nuc'):.6f}")
print("BY = BK S, S symmetric PD:")
for t in range(3):
    Bk = rng.standard_normal((3, 3)); S = rng.standard_normal((3, 3)); S = S @ S.T + 0.5 * np.eye(3)
    K, Y = ct(Bk, Bk @ S); print(f"  N={N_of(Y@K):.6f}  nuc={np.linalg.norm(Y@K,'nuc'):.6f}")
# normal perturbation at a maximiser (ascent endpoint)
A = np.load('logs/e12_n6_s3_e05_n6_s1_e0.05_best.npy_end0.npy')
u, s, vt = np.linalg.svd(core.BK(A)); K = skew_of(vt[0], 6); Y = skew_of(u[:, 0], 6)
print("endpoint pair N =", N_of(Y @ K))
for t in range(2):
    E = skew_of(rng.standard_normal(15)); E /= np.linalg.norm(E)
    for e in [1e-1, 3e-2, 1e-2, 3e-3]:
        Ye = Y + e * E; Ye /= np.linalg.norm(Ye)
        print(f"   dir {t} e={e:.0e}: 1 - N = {1 - N_of(Ye @ K):.3e}")
