"""n=6 specifics: canonical K, projection of Y onto the 3 moment constraints, compatibility."""
import numpy as np
from bl import *

N = 6
SbN, KbN = bases(6)   # (21,6,6), (15,6,6)


def make_K(a, b, c):
    K = np.zeros((6, 6))
    K[0:2, 0:2] = a * J2; K[2:4, 2:4] = b * J2; K[4:6, 4:6] = c * J2
    return K


def abc_from_uv(u, v, eps=0.0):
    """map R^2 -> (a,b,c) with a^2+b^2+c^2 = 1/2, all >= eps-ish (positive octant of sphere via softplus-free squares)"""
    w = np.array([1.0, np.exp(u), np.exp(v)])   # positive weights
    w = w / np.linalg.norm(w) / np.sqrt(2)
    return w   # unsorted a,b,c (K canonical up to permutation, which is an O(6) symmetry)


def skew_from_vec(y):
    return np.tensordot(y, KbN, axes=(0, 0))


def vec_from_skew(Y):
    return np.einsum('iab,ab->i', KbN, Y)


def moments(K, Y):
    YK = Y @ K
    D = Y @ Y - K @ K
    m0 = np.trace(D)
    P = YK @ D
    m1 = np.trace(P)
    m2 = np.trace(YK @ P)
    return np.array([m0, m1, m2])


def moment_jac(K, Y):
    """3x15 Jacobian wrt coords of Y in Kb."""
    YK = Y @ K
    D = Y @ Y - K @ K
    J = np.zeros((3, 15))
    YK2 = YK @ YK
    for i in range(15):
        E = KbN[i]
        EK = E @ K
        dD = E @ Y + Y @ E
        # d(YK)^j
        dm0 = np.trace(dD)
        dm1 = np.trace(EK @ D) + np.trace(YK @ dD)
        # (YK)^2 : d = EK YK + YK EK
        d2 = EK @ YK + YK @ EK
        dm2 = np.trace(d2 @ D) + np.trace(YK2 @ dD)
        J[:, i] = (dm0, dm1, dm2)
    return J


def project_Y(K, y0, iters=30, tol=1e-15):
    y = y0.copy()
    for it in range(iters):
        Y = skew_from_vec(y)
        m = moments(K, Y)
        if np.linalg.norm(m) < tol:
            return y, np.linalg.norm(m), it
        Jm = moment_jac(K, Y)
        dy = np.linalg.lstsq(Jm, -m, rcond=1e-12)[0]
        # damp
        nd = np.linalg.norm(dy)
        if nd > 0.5:
            dy *= 0.5 / nd
        y = y + dy
    Y = skew_from_vec(y)
    return y, np.linalg.norm(moments(K, Y)), iters


def random_pair(rng, abc=None, ymode='gauss'):
    if abc is None:
        w = rng.uniform(0.05, 1, 3); w = w / np.linalg.norm(w) / np.sqrt(2); abc = w
    K = make_K(*abc)
    y0 = rng.standard_normal(15); y0 /= np.linalg.norm(y0)
    y, err, it = project_Y(K, y0)
    return K, skew_from_vec(y), err
