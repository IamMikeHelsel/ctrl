"""E04: test conjecture SS_n: for every A and every skew singular triple (sigma,K,Y) of L_A|K,
   max_{T in T(K)} ||L_A(K T)|| >= sigma ||K||   (T sym. involution anticommuting with K, torus family)
ratio rho = max_T ||L_A(KT)|| / sigma.  Equivalent (n=6, K invertible) to g_K >= 1 on all compatible pairs.
Prints worst ratios. modes: gauss, sparse, nonneg-mix, lowrank, n7 (positive control: needs kernel handling)."""
import sys, json
import numpy as np
from core import *
from ssclass import comp_mats, oracle, dvec

def rho_all(A, top_only=False):
    Bk = BK(A); u, s, vt = np.linalg.svd(Bk)
    out = []
    rng_ = range(1) if top_only else range(len(s))
    for i in rng_:
        K = skew_of(vt[i], A.shape[0])
        sv = np.linalg.svd(K, compute_uv=False)
        Xs, F = comp_mats(K)
        V = np.array([L(A, X).ravel() for X in Xs])
        best = oracle(V, k=1)[0][0]
        out.append((np.sqrt(best) / s[i], s[i] / s[0], sv[-1], i))
    return out

if __name__ == '__main__':
    seed = int(sys.argv[1]); N = int(sys.argv[2]); mode = sys.argv[3]
    rng = np.random.default_rng(seed)
    worst = []
    allmin = np.inf
    for k in range(N):
        A = rng.standard_normal((6, 6))
        if mode == 'sparse': A *= rng.random((6, 6)) < rng.uniform(0.2, 0.8)
        if mode == 'scaled': A = A * np.exp(rng.standard_normal((6, 6)))
        if mode == 'lowrank':
            r = rng.integers(1, 4); A = rng.standard_normal((6, r)) @ rng.standard_normal((r, 6))
        if mode == 'skewish': A = A - A.T + 0.3 * rng.standard_normal((6, 6))
        res = rho_all(A)
        for rho, rel, smin, i in res:
            if rho < allmin: allmin = rho
            if rho < 1 + 1e-6:
                worst.append(dict(k=k, i=i, rho=rho, rel=rel, smin=smin, A=A.tolist()))
                print(json.dumps(dict(k=k, i=i, rho=rho, rel=rel, smin=smin)), flush=True)
        if k % 25 == 0: print(f"# {k} done, min rho so far {allmin:.8f}", flush=True)
    print(f"# FINAL min rho {allmin:.10f}, #rho<1+1e-6: {len(worst)}")
    json.dump(worst[:200], open(f'logs/e04_{mode}_{seed}_worst.json', 'w'))
