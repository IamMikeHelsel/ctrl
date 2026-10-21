"""E08: single-test-matrix certificate
   h(K,Y) = max_{V sym} min_z ||L_{A(z)} V|| / ||V||  =  max_V ||Pi_V^perp L_{A0} V|| / ||V||,
Pi_V = orthogonal projector onto span{L_{A_r} V}.  h <= f, with equality when the optimal dual has rank 1.
Local maximisation (BFGS) from the f-dual right vectors and from random starts."""
import sys, warnings
warnings.filterwarnings('ignore')
import numpy as np
from scipy.optimize import minimize
from core import *
from e07_dual_at import top_pair

def make_h(A0, Ar):
    def hval(v):
        V = sym_of(v); nv = np.linalg.norm(V)
        b = L(A0, V).ravel(); C = np.array([L(Ai, V).ravel() for Ai in Ar]).T
        z, *_ = np.linalg.lstsq(C, -b, rcond=None)
        return np.linalg.norm(b + C @ z) / nv
    return hval

def h_of_pair(K, Y, nrand=10, seed=0):
    f, A, W, info = inner_cvx(K, Y)
    A0, Ar = info['A0'], info['Ar']
    hval = make_h(A0, Ar)
    starts = [scoords(V) for s, U, V in dual_terms(W, cut=1e-3)]
    rng = np.random.default_rng(seed)
    starts += [rng.standard_normal(21) for _ in range(nrand)]
    best = (-1, None)
    for x0 in starts:
        r = minimize(lambda v: -hval(v), x0, method='BFGS', options=dict(gtol=1e-10, maxiter=3000))
        if -r.fun > best[0]: best = (-r.fun, r.x)
    return f, best[0], sym_of(best[1]) / np.linalg.norm(sym_of(best[1])), len(dual_terms(W, cut=1e-3))

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1].endswith('.npy'):
        K, Y, s = top_pair(np.load(sys.argv[1]))
        f, h, V, rk = h_of_pair(K, Y)
        print(f"{sys.argv[1]}: f={f:.6f} h={h:.6f} dual rank {rk}")
    else:
        seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
        rng = np.random.default_rng(seed)
        for k in range(int(sys.argv[2]) if len(sys.argv) > 2 else 8):
            K, Y, err = random_pair(rng)
            f, h, V, rk = h_of_pair(K, Y)
            print(f"pair {k}: f={f:.6f} h={h:.6f} dual rank {rk}  V eig {np.round(np.linalg.eigvalsh(V),3)}", flush=True)
