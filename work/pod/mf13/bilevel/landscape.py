"""Distribution of f over random compatible pairs; two samplers."""
import numpy as np, sys, time, json
from evalf import *

mode = sys.argv[1]; N = int(sys.argv[2]); seed = int(sys.argv[3])
rng = np.random.default_rng(seed)
rows = []
t0 = time.time()
for it in range(N):
    if mode == 'gauss':
        w = rng.uniform(0.02, 1, 3); w = w / np.linalg.norm(w) / np.sqrt(2)
        K = make_K(*w)
        y0 = rng.standard_normal(15); y0 /= np.linalg.norm(y0)
        y, err, _ = project_Y(K, y0)
        Y = skew_from_vec(y)
        if err > 1e-12: continue
    elif mode == 'fromA':
        # natural sampler: random A -> top skew pair, rotated to canonical K
        A = rng.standard_normal((6, 6))
        sig, K0, Y0, sv = skew_top_pair(A)
        # canonical form of K0: real Schur of skew matrix
        from scipy.linalg import schur
        T, Z = schur(K0, output='real')
        # blocks of T are 2x2 [[0,x],[-x,0]] (possibly sorted arbitrarily); sort descending |x|
        xs = np.array([T[0, 1], T[2, 3], T[4, 5]])
        # make positive via sign flip
        order = np.argsort(-np.abs(xs))
        P = np.zeros((6, 6))
        for newb, oldb in enumerate(order):
            P[2*newb:2*newb+2, 2*oldb:2*oldb+2] = np.eye(2) if xs[oldb] > 0 else np.diag([1., -1.])
        Q = Z @ P.T  # K0 = Q Kc Q^T
        Kc = Q.T @ K0 @ Q
        K, Y = Kc, Q.T @ Y0 @ Q
    out = f_of_pair(K, Y)
    sKmin = np.linalg.svd(K, compute_uv=False)[-1]; sYmin = np.linalg.svd(Y, compute_uv=False)[-1]
    rows.append((out['f'], sKmin, sYmin, out['nullity'], out['kept_sv']))
    if it % 50 == 0:
        a = np.array([r[0] for r in rows])
        print(it, f"min f {a.min():.5f} median {np.median(a):.4f}  time {time.time()-t0:.0f}s", flush=True)
rows = np.array(rows)
np.save(f'landscape_{mode}_{seed}.npy', rows)
f = rows[:, 0]
print("N", len(f), "min", f.min(), "q01", np.quantile(f, .01), "q10", np.quantile(f, .1), "median", np.median(f), "max", f.max())
i = np.argmin(f); print("argmin row", rows[i])
print("nullity counts", np.unique(rows[:, 3], return_counts=True))
