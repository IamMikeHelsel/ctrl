"""E07: f(K,Y) and the optimal dual certificate at a given A's top skew pair (or a random pair).
Prints: f, g_K, dual weights, and for each dual term (sig, U, V): eigenvalues of V, |V^2+K^2|, |VK+KV|, |U^2+Y^2|, |UY+YU|,
and the decomposition of P = sum sig V U into K Z1 + Z2 Y (least squares, residual)."""
import sys, warnings
warnings.filterwarnings('ignore')
import numpy as np
from core import *
from ssclass import g_K
np.set_printoptions(precision=4, suppress=True, linewidth=160)

def top_pair(A):
    u, s, vt = np.linalg.svd(BK(A))
    K = skew_of(vt[0]); Y = skew_of(u[:, 0])
    if np.sum(Y * L(A, K)) < 0: Y = -Y
    return K, Y, s[0]

def decompose_P(P, K, Y):
    """P = K Z1 + Z2 Y, Z skew: least squares in 30 unknowns."""
    Kb = bases(6)[1]
    cols = [(K @ E).ravel() for E in Kb] + [(E @ Y).ravel() for E in Kb]
    Mx = np.array(cols).T
    c, *_ = np.linalg.lstsq(Mx, P.ravel(), rcond=None)
    Z1 = np.tensordot(c[:15], Kb, axes=(0, 0)); Z2 = np.tensordot(c[15:], Kb, axes=(0, 0))
    return Z1, Z2, np.linalg.norm(Mx @ c - P.ravel())

def analyse(K, Y, label=""):
    f, A, W, info = inner_cvx(K, Y)
    g = g_K(K, Y)
    print(f"== {label} f = {f:.8f}   g_K = {g[1]:.8f}   s,k(A*) = {norms(A)}")
    terms = dual_terms(W, cut=1e-4)
    P = np.zeros((6, 6)); tot = 0
    for sig, U, V in terms:
        P += sig * V @ U; tot += sig
        print(f"  sig={sig:.4f} V eig={np.linalg.eigvalsh(V)} |V2+K2|={np.linalg.norm(V@V+K@K):.3f} |VK+KV|={np.linalg.norm(V@K+K@V):.3f}"
              f" |U2+Y2|={np.linalg.norm(U@U+Y@Y):.3f} |UY+YU|={np.linalg.norm(U@Y+Y@U):.3f}  <U,L V>={np.sum(U*L(A,V)):.6f}")
    Z1, Z2, res = decompose_P(P, K, Y)
    print(f"  sum sig = {tot:.6f};  P = K Z1 + Z2 Y residual {res:.2e};  value tr(Z1Y)+tr(Z2K) = {np.trace(Z1@Y)+np.trace(Z2@K):.6f}")
    return f, A, W, terms, Z1, Z2

if __name__ == '__main__':
    if len(sys.argv) > 1:
        A = np.load(sys.argv[1]); K, Y, s = top_pair(A)
        analyse(K, Y, sys.argv[1])
    else:
        rng = np.random.default_rng(0)
        for k in range(3):
            K, Y, err = random_pair(rng); analyse(K, Y, f"random pair {k}")
