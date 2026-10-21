"""E09: structure of the optimal single test matrix V* (and U* = L_{A*}V*/f) across pairs.
Reports eigenvalues of V* and U*, moduli of K and Y, Gram/commutation diagnostics, and fits
V* in span of candidate symmetric matrices built from K, Y (least squares, relative residual)."""
import sys, warnings
warnings.filterwarnings('ignore')
import numpy as np
from core import *
from e08_single_V import h_of_pair
from e07_dual_at import top_pair
np.set_printoptions(precision=3, suppress=True, linewidth=170)

def candidates(K, Y):
    I = np.eye(6); Ki = np.linalg.inv(K); Yi = np.linalg.inv(Y)
    S = lambda X: (X + X.T) / 2
    c = dict(I=I, K2=K@K, Y2=Y@Y, KY=S(K@Y), K4=K@K@K@K, Y4=Y@Y@Y@Y, KYYK=K@Y@Y@K, YKKY=Y@K@K@Y,
             K2Y2=S(K@K@Y@Y), KYKY=S(K@Y@K@Y), K3Y=S(K@K@K@Y), KY3=S(K@Y@Y@Y),
             KiY=S(Ki@Y), KYi=S(K@Yi), Ki2=Ki@Ki, Yi2=Yi@Yi, KiYi=S(Ki@Yi))
    return c

def fit(V, cands):
    names = list(cands); M = np.array([cands[k].ravel() for k in names]).T
    c, *_ = np.linalg.lstsq(M, V.ravel(), rcond=None)
    return np.linalg.norm(M @ c - V.ravel()) / np.linalg.norm(V), dict(zip(names, c))

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
pairs = []
for k in range(5):
    pairs.append(('gauss', *random_pair(rng)[:2]))
for k in range(3):
    A = rng.standard_normal((6, 6)); K, Y, s = top_pair(A); pairs.append(('nat', K, Y))
K, Y, s = top_pair(np.load('logs/e05_n6_s1_e0.05_best.npy')); pairs.append(('ssfail', K, Y))
for lab, K, Y in pairs:
    f, h, V, rk = h_of_pair(K, Y, nrand=6)
    f2, A, W, info = inner_cvx(K, Y)
    U = L(A, V); U /= np.linalg.norm(U)
    mk = np.linalg.svd(K, compute_uv=False)[::2]; my = np.linalg.svd(Y, compute_uv=False)[::2]
    r1, c1 = fit(V, candidates(K, Y))
    print(f"[{lab}] f={f:.5f} h={h:.5f} rk={rk} |K|mod={mk} |Y|mod={my}")
    print(f"     eig V*={np.linalg.eigvalsh(V)}  eig U*={np.linalg.eigvalsh(U)}  poly-fit resid V*={r1:.3f}")
    print(f"     |[V,K^2]|={np.linalg.norm(V@K@K-K@K@V):.3f} |VK+KV|={np.linalg.norm(V@K+K@V):.3f} |V^2+K^2|={np.linalg.norm(V@V+K@K):.3f}"
          f"  |[U,Y^2]|={np.linalg.norm(U@Y@Y-Y@Y@U):.3f} |UY+YU|={np.linalg.norm(U@Y+Y@U):.3f}", flush=True)
