import numpy as np
from scipy.optimize import minimize

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

def project_Y(K, Y_init):
    K2 = K @ K
    def moments(y_vec):
        Y = sum(y_vec[i] * K_basis[i] for i in range(15))
        YK = Y @ K
        Y2_K2 = Y @ Y - K2
        m0 = np.trace(Y2_K2)
        m1 = np.trace(YK @ Y2_K2)
        m2 = np.trace((YK @ YK) @ Y2_K2)
        return np.array([m0, m1, m2])
    
    y = np.array([np.sum(Y_init * B) for B in K_basis], dtype=float)
    for _ in range(15):
        m = moments(y)
        if np.linalg.norm(m) < 1e-15:
            break
        J = np.zeros((3, 15))
        eps = 1e-8
        for k in range(15):
            y_p = y.copy(); y_p[k] += eps
            J[:, k] = (moments(y_p) - m) / eps
        dy, _, _, _ = np.linalg.lstsq(J, -m, rcond=None)
        y = y + dy
    Y_sol = sum(y[i] * K_basis[i] for i in range(15))
    return Y_sol, np.linalg.norm(moments(y))

def solve_pair(K, Y):
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
    
    _, s_phi, vt_phi = np.linalg.svd(Phi)
    null_basis = vt_phi[rank:].T
    
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
    
    def get_BS(A):
        BS = np.zeros((21, 21))
        for col, X in enumerate(S_basis):
            LX = A @ X + X @ A.T
            for row, W in enumerate(S_basis):
                BS[row, col] = np.sum(LX * W)
        return BS
        
    BS0 = get_BS(A0)
    BS_null = [get_BS(Ak) for Ak in A_null]
    
    def obj_and_grad(z):
        BS = BS0.copy()
        for k, zk in enumerate(z):
            BS += zk * BS_null[k]
        u, s, vt = np.linalg.svd(BS)
        u0 = u[:, 0]
        v0 = vt[0, :]
        grad = np.array([u0 @ BS_null[k] @ v0 for k in range(len(z))])
        return s[0], grad
        
    res = minimize(obj_and_grad, np.zeros(len(BS_null)), jac=True, method='BFGS')
    res2 = minimize(lambda z: obj_and_grad(z)[0], res.x, method='Nelder-Mead', options={'maxiter': 1500, 'xatol': 1e-9, 'fatol': 1e-9})
    return res2.fun, res_norm

if __name__ == '__main__':
    print("Testing 10 random general compatible pairs (K, Y):")
    min_overall = 1e9
    for i in range(10):
        svals = np.random.uniform(0.1, 1.0, 3)
        svals = svals / np.sqrt(2 * np.sum(svals**2))
        K = make_K(*svals)
        M = np.random.randn(6, 6); Y_init = M - M.T
        Y_init = Y_init / np.linalg.norm(Y_init)
        Y, m_err = project_Y(K, Y_init)
        if m_err < 1e-12 and np.linalg.svd(Y, compute_uv=False)[-1] > 1e-2:
            s_min, res_norm = min_sym_norm_for_pair(K, Y)
            if s_min is not None:
                min_overall = min(min_overall, s_min)
                print(f"Pair {i:2d}: min ||L_A|_S|| = {s_min:.8f} (res={res_norm:.1e}, sv_min(Y)={np.linalg.svd(Y, compute_uv=False)[-1]:.3f})")
    print("Minimum over tested compatible pairs:", min_overall)
