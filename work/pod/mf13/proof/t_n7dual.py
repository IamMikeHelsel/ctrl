"""The N-SDP dual variable G is a matrix A with <A,YK> = N(YK) and s(A)/2 <= 1 (dual-norm ball).
Check independently via BS/BK that A_G := G (suitably transposed/scaled) has k/s >= N for the n=7 KV pair."""
import warnings; warnings.filterwarnings('ignore')
import numpy as np
from core import *
from staticN import N_of
A7 = np.array([[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[6,-5,-13,0,0,0,0],[-14,-18,0,0,0,0,0],[12,-12,11,0,0,0,0],[0,0,0,-6,0,-14,0],[0,0,0,6,-18,0,0]],float)
def ratio(A): return np.linalg.norm(BK(A),2)/np.linalg.norm(BS(A),2)
print("KV ratio k/s =", ratio(A7))
u,s,vt = np.linalg.svd(BK(A7)); K = skew_of(vt[0],7); Y = skew_of(u[:,0],7)
N, W, G = N_of(Y@K, return_W=True)
print("N(YK) =", N)
for cand in [G, G.T, -G, -G.T]:
    print("  candidate ratio:", ratio(cand))
Abest = max([G, G.T], key=ratio)
# polish: iterate A <- dual of N at top pair of A (alternating ascent)
A = Abest.copy()
for it in range(30):
    u,s,vt = np.linalg.svd(BK(A)); K = skew_of(vt[0],7); Y = skew_of(u[:,0],7)
    N, W, G = N_of(Y@K, return_W=True)
    A = max([G, G.T], key=ratio)
    if it % 5 == 0 or it == 29: print(it, "N =", N, "ratio =", ratio(A))
np.save('logs/n7_dual_best.npy', A)
print(np.array2string(A/np.abs(A).max(), precision=4, suppress_small=True))
