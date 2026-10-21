"""Classify MM-ascent endpoints A: top skew pair (K,Y), ratio, moduli, common-T defect.
common-T defect := smallest singular value of S -> (SK+KS, SY+YS) on unit symmetric S (0 iff a symmetric S anticommutes
with both; then T can be taken an involution generically), and the defect of the best involution found."""
import sys, glob, numpy as np
from core import *
def ratio(A): return np.linalg.norm(BK(A),2)/np.linalg.norm(BS(A),2)
def ct_defect(K, Y):
    n = K.shape[0]; Sb = bases(n)[0]
    M = np.array([np.concatenate([(S@K+K@S).ravel(), (S@Y+Y@S).ravel()]) for S in Sb]).T
    u, s, vt = np.linalg.svd(M); S = np.tensordot(vt[-1], Sb, 1)
    return s[-1], np.round(np.linalg.eigvalsh(S/np.abs(np.linalg.eigvalsh(S)).max()), 3)
for fn in sorted(sys.argv[1:]):
    A = np.load(fn); n = A.shape[0]
    u, s, vt = np.linalg.svd(BK(A)); K = skew_of(vt[0], n); Y = skew_of(u[:, 0], n)
    d, ev = ct_defect(K, Y)
    print(f"{fn.split('/')[-1]}: ratio={ratio(A):.10f} k2/k1={s[1]/s[0]:.4f} mK={np.round(np.linalg.svd(K,compute_uv=False)[::2],4)} "
          f"mY={np.round(np.linalg.svd(Y,compute_uv=False)[::2],4)} cT-defect={d:.2e} eig(S)={ev}")
