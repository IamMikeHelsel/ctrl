"""E10: adversarial minimisation over compatible pairs of a class value g_C(K,Y).
Pair parametrisation (bilevel Track A): (u,v) -> K = diag(aJ,bJ,cJ), a^2+b^2+c^2=1/2;  15 raw Y coords -> normalise -> project on moments.
objective = g_C + 50*max(0, eps - min modulus(K)) + 50*max(0, eps - min modulus(Y))   [moduli of unit-norm K,Y]
classes: C9K (right), C9Yl (left), either (C9K right OR C9Y left, pointwise), sum (C9K+C9Y right), full (= f)."""
import sys, json, warnings
warnings.filterwarnings('ignore')
import numpy as np
import cma
import cvxpy as cp
from core import *
from classes import class_Q

cls = sys.argv[1]; seed = int(sys.argv[2]); gens = int(sys.argv[3]); eps = float(sys.argv[4]) if len(sys.argv) > 4 else 0.05

def gval(K, Y):
    A0, Ar, res = affine_family(K, Y)
    if res > 1e-8 or len(Ar) != 9: return np.inf
    B0 = BS(A0); Br = [BS(Ai) for Ai in Ar]
    z = cp.Variable(9); t = cp.Variable()
    B = B0 + sum(z[i] * Br[i] for i in range(9))
    cons = []
    def lmi(M):
        a, b = M.shape
        return cp.bmat([[t * np.eye(a), M], [M.T, t * np.eye(b)]]) >> 0
    if cls in ('C9K', 'either'):
        cons.append(lmi(B @ class_Q(K, Y, 'C9K')))
    if cls in ('C9Yl', 'either'):
        cons.append(lmi(class_Q(K, Y, 'C9Y').T @ B))
    if cls == 'sum':
        cons.append(lmi(B @ class_Q(K, Y, 'C9K+C9Y')))
    if cls == 'full':
        cons.append(lmi(B))
    if cls == 'either':
        # pointwise either/or: min_z max(t1,t2) is the same as one t with both LMIs
        pass
    prob = cp.Problem(cp.Minimize(t), cons)
    try:
        prob.solve(solver=cp.CLARABEL)
    except Exception:
        return np.inf
    return float(t.value) if t.value is not None else np.inf

def pair_from_x(x):
    w = np.array([1.0, np.exp(x[0]), np.exp(x[1])]); w = w / np.linalg.norm(w) / np.sqrt(2)
    K = make_K(*w)
    Y0 = skew_of(x[2:17]); nY = np.linalg.norm(Y0)
    if nY < 1e-8: return None, None
    Y, err = project_Y(K, Y0 / nY)
    if err > 1e-12: return None, None
    return K, Y

def obj(x):
    K, Y = pair_from_x(x)
    if K is None: return 10.0
    mk = np.linalg.svd(K, compute_uv=False)[-1]; my = np.linalg.svd(Y, compute_uv=False)[-1]
    g = gval(K, Y)
    return g + 50 * max(0, eps - mk) + 50 * max(0, eps - my)

rng = np.random.default_rng(seed)
x0 = np.concatenate([rng.normal(0, 0.5, 2), rng.standard_normal(15)])
es = cma.CMAEvolutionStrategy(x0, 0.5, dict(seed=seed, verbose=-9, popsize=16))
best = (np.inf, None)
for g in range(gens):
    X = es.ask(); F = [obj(np.array(x)) for x in X]
    es.tell(X, F)
    i = int(np.argmin(F))
    if F[i] < best[0]: best = (F[i], np.array(X[i]))
    if g % 10 == 0 or g == gens - 1:
        K, Y = pair_from_x(best[1])
        print(json.dumps(dict(g=g, best=best[0], mK=np.round(np.linalg.svd(K, compute_uv=False)[::2], 4).tolist(),
                              mY=np.round(np.linalg.svd(Y, compute_uv=False)[::2], 4).tolist())), flush=True)
        np.save(f'logs/e10_{cls}_s{seed}_best.npy', best[1])
