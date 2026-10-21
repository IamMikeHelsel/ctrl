"""Sample structured A (to hit degenerate strata of pairs) and compute f(top skew pair of A)."""
import sys, time
import numpy as np
from bl import *
from barrier import barrier_min_sigma

n = 6
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
J6 = np.kron(np.eye(3), J2)


def f_from_A(A, tol=1e-9):
    sig, K, Y, sv = skew_top_pair(A)
    A0, Ar, resid, rank = affine_family(K, Y)
    if resid > 1e-7: return np.nan, -1, sv
    B0 = BS(A0); Br = np.array([BS(a) for a in Ar])
    fv, z, t, nit = barrier_min_sigma(B0, Br, tol=tol)
    return fv, len(Ar), sv


def blockdiag(sizes):
    A = np.zeros((n, n)); o = 0
    for s in sizes:
        A[o:o+s, o:o+s] = rng.standard_normal((s, s)); o += s
    return A


def cls(name):
    g = rng.standard_normal((n, n))
    if name == 'blk33': return blockdiag([3, 3])
    if name == 'blk24': return blockdiag([2, 4])
    if name == 'blk222': return blockdiag([2, 2, 2])
    if name == 'blk51': return blockdiag([5, 1])
    if name == 'blk111111': return np.diag(rng.standard_normal(n))
    if name == 'blk42': return blockdiag([4, 2])
    if name == 'cplx':   # commute with J6: A = sum X_ij (x) (a + b J)
        a = rng.standard_normal((3, 3)); b = rng.standard_normal((3, 3))
        return np.kron(a, np.eye(2)) + np.kron(b, J2)
    if name == 'anticplx':  # anticommute-ish: A = X (x) R0 + Y (x) R1 (3x3 real blocks times reflections)
        a = rng.standard_normal((3, 3)); b = rng.standard_normal((3, 3))
        return np.kron(a, np.diag([1., -1.])) + np.kron(b, np.array([[0., 1.], [1., 0.]]))
    if name == 'sym': return g + g.T
    if name == 'skew': return g - g.T
    if name == 'normal':
        Q = np.linalg.qr(g)[0]; D = np.zeros((n, n))
        for i in range(3):
            D[2*i:2*i+2, 2*i:2*i+2] = rng.standard_normal() * np.eye(2) + rng.standard_normal() * J2
        return Q @ D @ Q.T
    if name == 'tri': return np.triu(g)
    if name == 'lowtri': return np.tril(g)
    if name == 'rank3': return rng.standard_normal((n, 3)) @ rng.standard_normal((3, n))
    if name == 'rank2': return rng.standard_normal((n, 2)) @ rng.standard_normal((2, n))
    if name == 'nilp': 
        N_ = np.triu(g, 1); Q = np.linalg.qr(rng.standard_normal((n, n)))[0]; return Q @ N_ @ Q.T
    if name == 'sympsd_plus_skew':
        P = g @ g.T; S = rng.standard_normal((n, n)); return P + 0.5 * (S - S.T)
    if name == 'perm': 
        P = np.eye(n)[rng.permutation(n)]; return P * rng.standard_normal()+ 0.1 * g
    return g

names = ['gauss', 'blk33', 'blk24', 'blk42', 'blk222', 'blk51', 'blk111111', 'cplx', 'anticplx', 'sym', 'skew', 'normal', 'tri', 'rank3', 'rank2', 'nilp', 'sympsd_plus_skew', 'perm']
for nm in names:
    fs = []; nl = []
    t0 = time.time()
    for _ in range(N):
        A = cls(nm)
        try:
            fv, nul, sv = f_from_A(A)
        except Exception as e:
            continue
        if np.isfinite(fv): fs.append(fv); nl.append(nul)
    fs = np.array(fs); nl = np.array(nl)
    print(f"{nm:18s} N={len(fs):4d} min f={fs.min():.8f} q10={np.quantile(fs,.1):.5f} med={np.median(fs):.5f} nullities={dict(zip(*np.unique(nl, return_counts=True)))} below1: {(fs<1-1e-9).sum()}  [{time.time()-t0:.0f}s]", flush=True)
