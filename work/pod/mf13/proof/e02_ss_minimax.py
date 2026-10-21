"""E02: does the same-square comparator class suffice POINTWISE in z?
 g_K(K,Y) = min_z max_{T in T^3_K} ||L_{A(z)}(KT)||     (Chen-Tian class, K side, U arbitrary)
 g_KY     = min_z max( max_T ||L_{A(z)}(KT)||, max_{T' in T^3_Y} ||L_{A(z)^T}(Y T')|| )
Both are convex in z (max of norms of affine maps). Cutting-plane SOCP.
Compare with f(K,Y).  If g < 1 for some pair, the same-square class cannot prove n=6."""
import sys
import numpy as np
import cvxpy as cp
from scipy.optimize import minimize
from scipy.linalg import schur
from core import *

def refl(t):
    return np.array([[np.cos(t), np.sin(t)], [np.sin(t), -np.cos(t)]])

def frame(X):
    """real Schur frame of skew X: X = F diag(w_i J) F^T."""
    Tm, Z = schur(X, output='real')
    w = np.array([Tm[0, 1], Tm[2, 3], Tm[4, 5]])
    return Z, w

def Tof(F, th):
    T0 = np.zeros((6, 6))
    for i in range(3): T0[2*i:2*i+2, 2*i:2*i+2] = refl(th[i])
    return F @ T0 @ F.T

def g_value(K, Y, sides=('K',), ncut=200, tol=1e-7, seed=0, verbose=False):
    rng = np.random.default_rng(seed)
    A0, Ar, res = affine_family(K, Y)
    FK, _ = frame(K); FY, _ = frame(Y)
    r = len(Ar)
    def vec(side, th):
        # returns (c0, C) with L(A(z)) X = c0 + C z (as 36-vectors), X unit
        if side == 'K':
            X = K @ Tof(FK, th); X /= np.linalg.norm(X)
            c0 = L(A0, X).ravel(); C = np.array([L(Ai, X).ravel() for Ai in Ar]).T
        else:
            X = Y @ Tof(FY, th); X /= np.linalg.norm(X)
            c0 = L(A0.T, X).ravel(); C = np.array([L(Ai.T, X).ravel() for Ai in Ar]).T
        return c0, C
    def oracle(z):
        best = (-1, None)
        for side in sides:
            def neg(th):
                c0, C = vec(side, th); return -np.linalg.norm(c0 + C @ z)
            grid = rng.uniform(0, 2*np.pi, (40, 3))
            vals = [neg(g) for g in grid]
            for i in np.argsort(vals)[:4]:
                rr = minimize(neg, grid[i], method='BFGS')
                if -rr.fun > best[0]: best = (-rr.fun, (side, rr.x))
        return best
    cuts = [(s, rng.uniform(0, 2*np.pi, 3)) for s in sides for _ in range(10)]
    z = np.zeros(r); lo = 0
    for it in range(ncut):
        zv = cp.Variable(r); t = cp.Variable()
        cons = []
        for side, th in cuts:
            c0, C = vec(side, th); cons.append(cp.norm(c0 + C @ zv) <= t)
        cp.Problem(cp.Minimize(t), cons).solve(solver=cp.CLARABEL)
        lo = t.value; z = zv.value
        hi, arg = oracle(z)
        if verbose: print(it, lo, hi)
        if hi - lo < tol: break
        cuts.append(arg)
    return lo, hi

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    rng = np.random.default_rng(seed)
    for k in range(N):
        K, Y, err = random_pair(rng)
        f, A, info = inner_barrier(K, Y)
        gK = g_value(K, Y, ('K',), seed=k)
        gKY = g_value(K, Y, ('K', 'Y'), seed=k)
        print(f"pair {k}: f={f:.6f}  g_K in [{gK[0]:.6f},{gK[1]:.6f}]  g_KY in [{gKY[0]:.6f},{gKY[1]:.6f}]", flush=True)
