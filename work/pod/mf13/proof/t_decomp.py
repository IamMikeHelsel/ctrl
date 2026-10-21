import warnings; warnings.filterwarnings('ignore')
import numpy as np
from core import *
from staticN import N_of, decomposition
from e07_dual_at import top_pair
np.set_printoptions(precision=4, suppress=True, linewidth=150)
rng = np.random.default_rng(3)

def rel(X, Y): return np.linalg.norm(X - Y) / max(np.linalg.norm(X), 1e-300)

def analyse(K, Y, tag):
    K = K / np.linalg.norm(K); Y = Y / np.linalg.norm(Y)
    N, W, G = N_of(Y @ K, return_W=True)
    terms = decomposition(W, K.shape[0], 1e-5)
    print(f"--- {tag}: N={N:.6f}  sv(W)={np.round([t[0] for t in terms],5)}")
    for c, U, V in terms:
        # same-square tests: U^2 = -Y^2, V^2 = -K^2 (unit normalised); commutation with K^2, Y^2
        print(f"   c={c:.4f} |U^2+Y^2|={np.linalg.norm(U@U+Y@Y):.3f} |V^2+K^2|={np.linalg.norm(V@V+K@K):.3f}"
              f" |[V,K2]|={np.linalg.norm(V@K@K-K@K@V):.3f} |[U,Y2]|={np.linalg.norm(U@Y@Y-Y@Y@U):.3f}"
              f" eig(U)={np.round(np.linalg.eigvalsh(U),3)} eig(V)={np.round(np.linalg.eigvalsh(V),3)}")
    return N, terms, G

for t in range(3):
    K = skew_of(rng.standard_normal(15)); Y = skew_of(rng.standard_normal(15)); analyse(K, Y, f"random {t}")
for t in range(3):
    A = rng.standard_normal((6, 6)); K, Y, _ = top_pair(A); analyse(K, Y, f"natural {t}")
for fn in ['logs/e05_n6_s1_e0.05_best.npy']:
    K, Y, _ = top_pair(np.load(fn)); analyse(K, Y, "SS-fail")
