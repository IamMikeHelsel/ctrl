"""Custom log-barrier solver for  min_z sigma_max(B0 + sum_r z_r B_r)   (21x21 or any m x m).
Barrier: -logdet(t^2 I - B^T B) = -logdet [[tI,B],[B^T,tI]], self-concordant with parameter 2m."""
import numpy as np
from scipy.linalg import cho_factor, cho_solve


def barrier_min_sigma(B0, Br, tol=1e-9, z0=None, kappa0=None, max_newton=3000, verbose=False):
    Br = np.asarray(Br)
    r, m, _ = Br.shape
    I = np.eye(m)
    z = np.zeros(r) if z0 is None else z0.copy()
    B = B0 + np.tensordot(z, Br, axes=(0, 0))
    smax = np.linalg.norm(B, 2)
    t = 1.2 * smax + 1e-3 + 0.0
    kappa = kappa0 if kappa0 else 1.0 / t
    nu = 2.0 * m
    nit = 0
    BrT = np.transpose(Br, (0, 2, 1))
    while True:
        # Newton to center for this kappa
        for _ in range(60):
            B = B0 + np.tensordot(z, Br, axes=(0, 0))
            G = t * t * I - B.T @ B
            try:
                cf = cho_factor(G)
            except np.linalg.LinAlgError:
                raise RuntimeError("G not PD")
            Gi = cho_solve(cf, I)
            BGi = B @ Gi          # m x m
            # gradient
            gz = 2.0 * np.einsum('rij,ij->r', Br, BGi)
            gt = kappa - 2.0 * t * np.trace(Gi)
            g = np.concatenate([gz, [gt]])
            # dG_a
            C = np.empty((r + 1, m, m))
            C[:r] = -(np.einsum('rji,jk->rik', Br, B) + np.einsum('ji,rjk->rik', B, Br))  # -(Br^T B + B^T Br)
            C[r] = 2.0 * t * I
            GiC = np.einsum('ij,ajk->aik', Gi, C)   # Gi C_a
            H1 = np.einsum('aij,bji->ab', GiC, GiC)
            # second-order term: 2 tr(Gi Br^T Bs), tt: -2 tr(Gi)
            T = np.einsum('ij,rkj->rik', Gi, Br)    # (Gi Br^T)? shape r,m,m : T[r] = Gi @ Br[r]^T
            # tr(Gi Br^T Bs) = sum_ij (Gi Br^T)_{ij} Bs_{ji}
            H2 = 2.0 * np.einsum('rij,sji->rs', T, Br)
            H = H1.copy()
            H[:r, :r] += 0.5 * (H2 + H2.T)
            H[r, r] += -2.0 * np.trace(Gi)
            try:
                dx = -np.linalg.solve(H, g)
            except np.linalg.LinAlgError:
                dx = -np.linalg.lstsq(H, g, rcond=None)[0]
            dec2 = -g @ dx
            nit += 1
            if dec2 < 0 or not np.isfinite(dec2):
                dx = -g; dec2 = g @ g
            if dec2 / 2 < 1e-3 or nit > max_newton:
                break
            # line search: keep G PD and t>0, backtracking on merit
            def merit(zz, tt):
                Bb = B0 + np.tensordot(zz, Br, axes=(0, 0))
                Gg = tt * tt * I - Bb.T @ Bb
                try:
                    c = np.linalg.cholesky(Gg)
                except np.linalg.LinAlgError:
                    return np.inf
                if tt <= 0:
                    return np.inf
                return kappa * tt - 2.0 * np.log(np.diag(c)).sum()
            f0 = merit(z, t)
            s = 1.0 / (1.0 + np.sqrt(dec2)) if dec2 > 1 else 1.0
            for _ in range(60):
                fz = merit(z + s * dx[:r], t + s * dx[r])
                if fz <= f0 - 0.25 * s * dec2 * 0.5:
                    break
                s *= 0.5
            z = z + s * dx[:r]; t = t + s * dx[r]
        gap = nu / kappa
        if verbose:
            print(f"kappa {kappa:.3e} t {t:.12f} gap {gap:.2e} nit {nit}")
        if gap < tol * max(t, 1e-3) or nit > max_newton:
            break
        kappa *= 10.0
    B = B0 + np.tensordot(z, Br, axes=(0, 0))
    return np.linalg.norm(B, 2), z, t, nit
