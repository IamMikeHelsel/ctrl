"""f(K,Y) evaluator for n=6."""
import numpy as np
from n6 import *
from barrier import barrier_min_sigma


def f_of_pair(K, Y, tol=1e-8, want_z=False):
    """returns dict: f (upper bound sigma_max at returned z), resid, nullity, kept_sv, A (optimal A) """
    A0, Ar, resid, rank, s = affine_family(K, Y, return_info=True)
    out = dict(resid=resid, rank=rank, nullity=len(Ar), kept_sv=s[rank - 1] if rank > 0 else 0.0)
    if resid > 1e-8:
        out['f'] = np.inf
        return out
    B0 = BS(A0)
    Br = np.array([BS(A) for A in Ar])
    fval, z, t, nit = barrier_min_sigma(B0, Br, tol=tol)
    out['f'] = fval
    out['lb'] = t * (1 - 0)  # barrier t >= f_opt approx; actually t>=smax>=f
    out['nit'] = nit
    if want_z:
        out['z'] = z
        out['A'] = A0 + np.tensordot(z, Ar, axes=(0, 0))
        out['A0'] = A0; out['Ar'] = Ar
    return out


def Y_from_x(K, y):
    nrm = np.linalg.norm(y)
    if nrm < 1e-9:
        return None, np.inf
    yp, err, it = project_Y(K, y / nrm)
    return skew_from_vec(yp), err


def describe_pair(K, Y):
    sK = np.linalg.svd(K, compute_uv=False)
    sY = np.linalg.svd(Y, compute_uv=False)
    ev = np.linalg.eigvals(Y @ K)
    return dict(sK=sK[::2].tolist(), sY=sY[::2].tolist(), eig_YK=[complex(e) for e in ev[::2]])
