import numpy as np
from test_general_compatible import make_K, project_Y, solve_pair, min_sym_norm_for_pair, S_basis, K_basis

# Let's inspect the pair from test_outer_opt where min ||L_A|_S|| was ~ 1.00000010!
# Why did min ||L_A|_S|| approach 1.00000010?
# Wait: in test_outer_opt, what was Y when min ||L_A|_S|| approached 1.0?
# Let's check what happens when Y = ± K (or Y = Q K Q^T where Q commutes with K, or Y K has degenerate eigenvalues)!
# If Y = K, then A = I/2 is in the affine space of solutions (with H = 0),
# and for A = I/2, L_A(X) = X for ALL X, so ||L_A|_S|| = 1 and ||L_A|_K|| = 1!
# More generally, whenever A + A^T = ± I_6 (i.e. A = ± I_6 / 2 + W with W skew-symmetric),
#Wait: if A = ± I_6 / 2 + W with W skew-symmetric, then for ANY X:
# L_A(X) = ± X + (W X - X W).
# Since X -> W X - X W is skew-adjoint on matrix space (<X, W X - X W>_F = 0),
# ||L_A(X)||_F^2 = ||X||_F^2 + ||W X - X W||_F^2 >= ||X||_F^2!
# Wait: for A = I/2, ||L_A|_S|| = ||L_A|_K|| = 1!
# So (K, Y) = (K, K) ALWAYS has min_H ||L_A(H)|_S|| = 1 (attained at H = 0, A = I/2)!
# Wait: what if Y != K? Can min_H ||L_A(H)|_S|| EVER be < 1, or is it = 1 ONLY when A can have symmetric part ± I/2, OR even for general (K, Y) can min_H ||L_A(H)|_S|| reach 1?!

# Let's test! For a random compatible pair (K, Y) that is FAR from Y = ± K (say ||Y - K||_F >= 0.8 and ||Y + K||_F >= 0.8),
# what is the minimum of min_H ||L_A(H)|_S||?
for trial in range(10):
    svals = np.array([0.55, 0.38, 0.22])
    svals = svals / np.sqrt(2 * np.sum(svals**2))
    K = make_K(*svals)
    M = np.random.randn(6, 6); Y_init = M - M.T
    Y_init = Y_init / np.linalg.norm(Y_init)
    Y, m_err = project_Y(K, Y_init)
    dist_K = min(np.linalg.norm(Y - K), np.linalg.norm(Y + K))
    # Also check distance of eigenvalues of Y K from -K^2:
    # Note that by Cauchy-Schwarz, ||Y K||_F <= ||Y||_F ||K||_F, wait:
    s_min, res_norm = min_sym_norm_for_pair(K, Y)
    print(f"Trial {trial}: dist(Y, ±K) = {dist_K:.4f}, sv_min(Y) = {np.linalg.svd(Y, compute_uv=False)[-1]:.4f}, min ||L_A|_S|| = {s_min:.6f}")
