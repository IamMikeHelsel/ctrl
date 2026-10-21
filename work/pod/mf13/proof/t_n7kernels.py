"""n=7: kernel geometry of the top skew pair for KV's A and for the MM-ascended A; also N_7(P+0) = N_6(P) check."""
import warnings; warnings.filterwarnings('ignore')
import numpy as np
from core import *
from staticN import N_of
A7 = np.array([[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[6,-5,-13,0,0,0,0],[-14,-18,0,0,0,0,0],[12,-12,11,0,0,0,0],[0,0,0,-6,0,-14,0],[0,0,0,6,-18,0,0]],float)
def toppair(A):
    u,s,vt = np.linalg.svd(BK(A)); return skew_of(vt[0],7), skew_of(u[:,0],7), s
for name, A in [("KV", A7), ("MM", np.load('logs/n7_dual_best.npy'))]:
    K, Y, s = toppair(A)
    kK = np.linalg.svd(K)[2][-1]; kY = np.linalg.svd(Y)[2][-1]
    print(name, "moduli K", np.round(np.linalg.svd(K,compute_uv=False)[::2],4), "Y", np.round(np.linalg.svd(Y,compute_uv=False)[::2],4),
          " |<kerK,kerY>| =", abs(kK@kY), " k2/k1 =", s[1]/s[0])
    # interpolate Y's kernel toward K's kernel: rotate Y by the rotation taking kerY -> kerK in their plane
    v = kY - (kY@kK)*kK; v/=np.linalg.norm(v); c = kY@kK; th = np.arccos(np.clip(abs(c),0,1))
    for t in [0, 0.25, 0.5, 0.75, 1.0]:
        a = -t*th*np.sign(c) if c!=0 else -t*th
        # rotation in plane (kK, v) by angle a moving kY toward kK
        R = np.eye(7) + (np.cos(a)-1)*(np.outer(kK,kK)+np.outer(v,v)) + np.sin(a)*(np.outer(v,kK)-np.outer(kK,v))
        Yt = R@Y@R.T; Yt/=np.linalg.norm(Yt)
        print(f"   t={t:.2f} |<kerK,kerYt>|={abs(kK@np.linalg.svd(Yt)[2][-1]):.4f} N={N_of(Yt@K/np.linalg.norm(K)):.6f}")
# N_7(P+0) vs N_6(P)
rng = np.random.default_rng(0)
K6 = skew_of(rng.standard_normal(15)); Y6 = skew_of(rng.standard_normal(15)); P6 = Y6@K6
P7 = np.zeros((7,7)); P7[:6,:6] = P6
print("N6 =", N_of(P6), " N7(P+0) =", N_of(P7))
