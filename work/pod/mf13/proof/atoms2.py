"""Proximal-bundle computation of the atomic gauge N4(P) (see atoms.py for the atom set).
   N4(P) = 1 / min{ phi(G) : <G,P> = 1 },  phi(G) = max_{atoms a} <G,a>   (phi convex, cuts <G,a_i> exact minorants).
   Rigorous by construction:  LB_k := min_{<G,P>=1} max_i <G,a_i>  (LP over found atoms)  <=  min phi,
   so N4(P) <= 1/LB_k, and the LP dual is an explicit decomposition P = sum lam_i a_i, sum lam_i = 1/LB_k.
   Center starts at the N-SDP dual (feasible: phi <= 1/N there).  Oracle heuristic (only affects speed/tightness)."""
import numpy as np, cvxpy as cp
from scipy.optimize import linprog
from atoms import Atoms
from staticN import N_of

def lp_lower(P, atoms):
    n2 = P.size; A = np.array([a.ravel() for a in atoms])
    # min t s.t. A g <= t, P.g = 1   (var g, t)
    c = np.zeros(n2 + 1); c[-1] = 1
    Aub = np.hstack([A, -np.ones((len(atoms), 1))]); bub = np.zeros(len(atoms))
    Aeq = np.concatenate([P.ravel(), [0]])[None]; beq = [1.0]
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(None, None)] * (n2 + 1), method='highs')
    if r.status != 0: return -np.inf, None
    lam = -r.ineqlin.marginals
    return r.fun, lam

def N4_bundle(P, rng, iters=60, mu=1.0, verbose=False):
    n = P.shape[0]; At = Atoms(n); m = n * (n - 1) // 2
    Nv, W, G0 = N_of(P, return_W=True)
    cands = [g for g in (G0, -G0, G0.T, -G0.T) if np.sum(g * P) > 0]
    G0 = max(cands, key=lambda g: np.sum(g * P)); Gc = G0 / np.sum(G0 * P)
    atoms, warm = [], []
    def evalphi(G):
        found = At.oracle(G, rng, starts=3, warm=warm[-9:])
        for (s, f, x, a) in found[:8]:
            atoms.append(a); atoms.append(-a)
        warm.extend([(f, x) for (s, f, x, a) in found[:3]])
        return found[0][0]
    phic = evalphi(Gc); best_ub_phi = phic; hist = []
    for it in range(iters):
        Amat = np.array([a.ravel() for a in atoms])
        g = cp.Variable(n * n); t = cp.Variable()
        prob = cp.Problem(cp.Minimize(t + mu / 2 * cp.sum_squares(g - Gc.ravel())),
                          [Amat @ g <= t, P.ravel() @ g == 1])
        prob.solve(solver=cp.CLARABEL)
        Gn = g.value.reshape(n, n); model = t.value
        phin = evalphi(Gn)
        if phin <= phic - 0.1 * (phic - model): Gc, phic = Gn, phin   # serious step
        else: mu *= 1.5
        lb, lam = lp_lower(P, atoms)
        hist.append((it, phic, model, lb))
        if verbose: print(f"  it {it}: phi(center)={phic:.6f} model={model:.6f} LP-LB={lb:.6f} -> N4 <= {1/lb if lb>0 else np.inf:.6f}"
                          f"  (N = {Nv:.6f}, 1/phi(center) = {1/phic:.6f})  #atoms={len(atoms)} mu={mu:.2g}", flush=True)
        if lb > 0 and phic - lb < 1e-6: break
    np.save('logs/atoms2_center.npy', Gc)
    return Nv, (1 / lb if lb > 0 else np.inf), 1 / phic, hist
