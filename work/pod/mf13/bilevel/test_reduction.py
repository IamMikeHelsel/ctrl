"""Numerical verification of the theorist's reduction claims for n=6."""
import numpy as np
from n6 import *
rng = np.random.default_rng(1)

print("=== 1. moments: Jacobian check, projection")
K = make_K(0.5, 0.4, 0.2236)
y0 = rng.standard_normal(15); Y = skew_from_vec(y0)
Jn = moment_jac(K, Y)
eps = 1e-6
Jfd = np.array([(moments(K, skew_from_vec(y0 + eps*np.eye(15)[i])) - moments(K, skew_from_vec(y0 - eps*np.eye(15)[i])))/(2*eps) for i in range(15)]).T
print("jac err", np.abs(Jn-Jfd).max())

print("=== 2. incompatible Y (random) => inconsistent; projected Y => consistent; nullity")
for t in range(5):
    K = make_K(*abc_from_uv(*rng.standard_normal(2)))
    Yr = skew_from_vec(rng.standard_normal(15)); Yr /= np.linalg.norm(Yr)
    A0, Ar, resid, rank = affine_family(K, Yr)
    y, err, it = project_Y(K, vec_from_skew(Yr))
    Y = skew_from_vec(y)
    A0p, Arp, residp, rankp, s_ = affine_family(K, Y, return_info=True)
    print(f" raw: resid={resid:.3e} rank={rank} | projected(it={it}, moment err {err:.1e}): ||Y||={np.linalg.norm(Y):.6f} resid={residp:.2e} rank={rankp} nullity={len(Arp)} smallest kept sv={s_[rankp-1]:.2e}")

print("=== 3. YK eigenvalue multiplicity, cokernel claim (W0=K^-1, W1=Y, W2=YKY)")
for t in range(3):
    K, Y, err = random_pair(rng)
    ev = np.linalg.eigvals(Y @ K)
    ev = ev[np.argsort(ev.real)]
    print(" eig(YK):", np.round(ev, 5))
    # Phi
    SK = np.zeros((15, 21))
    KY = K @ Y; YK = Y @ K
    for c, H in enumerate(SbN):
        out = KY @ H - H @ YK
        SK[:, c] = np.einsum('iab,ab->i', KbN, out)
    u, s, vt = np.linalg.svd(SK)
    print("  Phi sv:", np.round(s, 6), " rank", (s > 1e-10).sum(), " ker dim", 21 - (s > 1e-10).sum())
    W = np.array([vec_from_skew(M) for M in (np.linalg.inv(K), Y, Y @ K @ Y)])
    print("  ||Phi^T W||:", np.linalg.norm(W @ SK), " rank[W]:", np.linalg.matrix_rank(W))
    cok = u[:, 12:]
    # W in span(cok)?
    print("  W in cokernel span residual:", np.linalg.norm(W.T - cok @ (cok.T @ W.T)))

print("=== 4. A(z) has (K,Y) as skew pair with sv 1; is it TOP skew sv? (random z in family)")
cnt_top = 0; tot = 0
tops = []
for t in range(40):
    K, Y, err = random_pair(rng)
    A0, Ar, resid, rank = affine_family(K, Y)
    if resid > 1e-9: continue
    for zscale in (0.0, 0.3, 1.0, 3.0):
        z = rng.standard_normal(len(Ar)) * zscale
        A = A0 + np.tensordot(z, Ar, axes=(0, 0))
        Bk = BK(A)
        sv = np.linalg.svd(Bk, compute_uv=False)
        # check pair eq and 1 in spectrum
        pe = np.linalg.norm(A@K+K@A.T-Y) + np.linalg.norm(A.T@Y+Y@A-K)
        has1 = np.abs(sv - 1).min()
        tops.append((zscale, sv[0], has1, pe))
        tot += 1; cnt_top += (sv[0] - 1 < 1e-9)
print(" fraction with 1 = top skew sv:", cnt_top, "/", tot)
for zs in (0.0, 0.3, 1.0, 3.0):
    arr = np.array([x for x in tops if x[0] == zs])
    print(f"  zscale {zs}: top skew sv mean {arr[:,1].mean():.3f} min {arr[:,1].min():.5f}; |sv-1| min {arr[:,2].max():.1e}; pair resid {arr[:,3].max():.1e}")
print("=== 5. dual statement: is (K,Y) a skew singular pair of A (K = right, Y = left)? check B_K v = u structure")
K, Y, err = random_pair(rng)
A0, Ar, resid, rank = affine_family(K, Y)
A = A0
Bk = BK(A)
kv = vec_from_skew(K); yv = vec_from_skew(Y)
print("  B_K kv - yv:", np.linalg.norm(Bk @ kv - yv), "  B_K^T yv - kv:", np.linalg.norm(Bk.T @ yv - kv))
