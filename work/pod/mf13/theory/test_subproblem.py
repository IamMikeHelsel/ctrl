import numpy as np
from scipy.optimize import minimize

# Wait: if Q = Q^T and Q^2 = I_6 (an orthogonal reflection across a k-dimensional subspace),
# AND Y = Q K Q (or Y = -Q K Q), let's check what happens to A!
# Wait: if Y = Q K Q, can we choose H0 Explicitly?!
# Let's check! Suppose Q = Q^T, Q^2 = I_6, and Y = Q K Q.
# We want (K Y) H - H (Y K) = K^3 - (Y^2 K + K Y^2)/2.
# Wait: what if we test solving (K Y) H - H (Y K) = RHS and then minimizing ||L_{A(H)}|_{S_6}|| over the 9D affine space of H?!
# Let's run a test right now on both:
# (a) Involutive pairs Y = ± Q K Q (where moments vanish identically!)
# (b) General compatible pairs (K, Y) obtained by projecting random Y onto the 3 moment equations!

J2 = np.array([[0., 1.], [-1., 0.]])
def make_K(a, b, c):
    K = np.zeros((6, 6))
    K[0:2, 0:2] = a * J2
    K[2:4, 2:4] = b * J2
    K[4:6, 4:6] = c * J2
    return K

S_basis = []
for i in range(6):
    M = np.zeros((6, 6)); M[i, i] = 1.0; S_basis.append(M)
for i in range(6):
    for j in range(i+1, 6):
        M = np.zeros((6, 6)); M[i, j] = M[j, i] = 1.0 / np.sqrt(2); S_basis.append(M)

K_basis = []
for i in range(6):
    for j in range(i+1, 6):
        M = np.zeros((6, 6)); M[i, j] = 1.0 / np.sqrt(2); M[j, i] = -1.0 / np.sqrt(2); K_basis.append(M)

def solve_pair(K, Y):
    # Solve (K Y) H - H (Y K) = K^3 - 0.5*(Y^2 K + K Y^2)
    KY = K @ Y
    YK = Y @ K
    RHS = K @ K @ K - 0.5 * (Y @ Y @ K + K @ Y @ Y)
    
    Phi = np.zeros((15, 21))
    for col, H in enumerate(S_basis):
        out = KY @ H - H @ YK
        for row, W in enumerate(K_basis):
            Phi[row, col] = np.sum(out * W)
            
    rhs_vec = np.array([np.sum(RHS * W) for W in K_basis])
    h0_vec, residuals, rank, s = np.linalg.lstsq(Phi, rhs_vec, rcond=1e-10)
    res_norm = np.linalg.norm(Phi @ h0_vec - rhs_vec)
    
    # Nullspace basis (21 x 9)
    _, s_phi, vt_phi = np.linalg.svd(Phi)
    null_basis = vt_phi[rank:].T # 21 x (21 - rank)
    
    H0 = sum(h0_vec[i] * S_basis[i] for i in range(21))
    H_null = [sum(null_basis[i, k] * S_basis[i] for i in range(21)) for k in range(null_basis.shape[1])]
    
    return H0, H_null, res_norm, rank

def min_sym_norm_for_pair(K, Y):
    H0, H_null, res_norm, rank = solve_pair(K, Y)
    if res_norm > 1e-8:
        return None, res_norm
    Kinv = np.linalg.inv(K)
    A0 = (H0 + 0.5 * Y) @ Kinv
    A_null = [Hk @ Kinv for Hk in H_null]
    
    # Precompute B_S matrices for A0 and A_null
    def get_BS(A):
        BS = np.zeros((21, 21))
        for col, X in enumerate(S_basis):
            LX = A @ X + X @ A.T
            for row, W in enumerate(S_basis):
                BS[row, col] = np.sum(LX * W)
        return BS
        
    BS0 = get_BS(A0)
    BS_null = [get_BS(Ak) for Ak in A_null]
    
    # Minimize largest singular value of BS0 + sum z_k BS_null[k]
    def obj(z):
        BS = BS0.copy()
        for k, zk in enumerate(z):
            BS += zk * BS_null[k]
        return np.linalg.svd(BS, compute_uv=False)[0]
        
    res = minimize(obj, np.zeros(len(BS_null)), method='BFGS')
    res2 = minimize(obj, res.x, method='Nelder-Mead', options={'maxiter': 2000, 'xatol': 1e-10, 'fatol': 1e-10})
    return res2.fun, res_norm

# Test 1: Involutive pairs Y = Q K Q with Q = Q^T, Q^2 = I
print("Testing involutive pairs Y = Q K Q:")
for trial in range(5):
    K = make_K(0.6, 0.35, np.sqrt(0.5 - 0.6**2 - 0.35**2))
    M = np.random.randn(6, 6); M = M + M.T
    _, U = np.linalg.eigh(M)
    D = np.diag([1, 1, 1, -1, -1, -1])
    Q = U @ D @ U.T
    Y = Q @ K @ Q.T
    s_min, res_norm = min_sym_norm_for_pair(K, Y)
    print(f"Trial {trial}: min ||L_A|_S|| = {s_min:.8f} (res = {res_norm:.2e})")
