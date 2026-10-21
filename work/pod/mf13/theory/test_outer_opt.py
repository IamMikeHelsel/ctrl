import numpy as np
from scipy.optimize import minimize
from test_general_compatible import make_K, project_Y, min_sym_norm_for_pair, K_basis

# Test outer optimization where we ALSO penalize ||Y - K||_F < 0.5 and ||Y + K||_F < 0.5
# so the optimizer cannot trivially walk to Y = ± K (where A = ± I/2 gives ||L_A|_S|| = 1)!

def eval_outer_nontrivial(x):
    svals = np.abs(x[:3]) + 0.12
    svals = svals / np.sqrt(2 * np.sum(svals**2))
    K = make_K(*svals)
    Y_init = sum(x[3+i] * K_basis[i] for i in range(15))
    if np.linalg.norm(Y_init) < 1e-6:
        return 10.0
    Y_init = Y_init / np.linalg.norm(Y_init)
    try:
        Y, m_err = project_Y(K, Y_init)
    except Exception:
        return 10.0
    if m_err > 1e-10:
        return 10.0 + m_err
    sv_Y = np.linalg.svd(Y, compute_uv=False)
    if sv_Y[-1] < 0.10:
        return 1.5 + 10.0 * (0.10 - sv_Y[-1])
    # Check distance of Y^2 from K^2 (or commutator [Y, K])
    comm_norm = np.linalg.norm(Y @ K - K @ Y)
    if comm_norm < 0.15:
        return 1.5 + 10.0 * (0.15 - comm_norm)
    s_min, res_norm = min_sym_norm_for_pair(K, Y)
    if s_min is None or res_norm > 1e-8:
        return 10.0
    return s_min

if __name__ == '__main__':
    for restart in range(3):
        x0 = np.random.randn(18)
        res = minimize(eval_outer_nontrivial, x0, method='Powell', options={'maxiter': 15, 'ftol': 1e-3})
        svals = np.abs(res.x[:3]) + 0.12
        svals = svals / np.sqrt(2 * np.sum(svals**2))
        K = make_K(*svals)
        Y_init = sum(res.x[3+i] * K_basis[i] for i in range(15))
        Y_init = Y_init / np.linalg.norm(Y_init)
        Y, _ = project_Y(K, Y_init)
        print(f"Restart {restart}: min ||L_A|_S|| = {res.fun:.6f}, ||[Y,K]||_F = {np.linalg.norm(Y@K - K@Y):.4f}, sv_min(Y) = {np.linalg.svd(Y, compute_uv=False)[-1]:.4f}")
