import numpy as np

A = np.array([
    [0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0],
    [6, -5, -13, 0, 0, 0, 0],
    [-14, -18, 0, 0, 0, 0, 0],
    [12, -12, 11, 0, 0, 0, 0],
    [0, 0, 0, -6, 0, -14, 0],
    [0, 0, 0, 6, -18, 0, 0]
], dtype=float)

def lyap_op_matrices(A):
    n = A.shape[0]
    S_basis = []
    for i in range(n):
        M = np.zeros((n, n))
        M[i, i] = 1.0
        S_basis.append(M)
    for i in range(n):
        for j in range(i+1, n):
            M = np.zeros((n, n))
            M[i, j] = 1.0 / np.sqrt(2)
            M[j, i] = 1.0 / np.sqrt(2)
            S_basis.append(M)
    K_basis = []
    for i in range(n):
        for j in range(i+1, n):
            M = np.zeros((n, n))
            M[i, j] = 1.0 / np.sqrt(2)
            M[j, i] = -1.0 / np.sqrt(2)
            K_basis.append(M)
    
    B_S = np.zeros((len(S_basis), len(S_basis)))
    for col, X in enumerate(S_basis):
        LX = A @ X + X @ A.T
        for row, Y in enumerate(S_basis):
            B_S[row, col] = np.sum(LX * Y)
            
    B_K = np.zeros((len(K_basis), len(K_basis)))
    for col, X in enumerate(K_basis):
        LX = A @ X + X @ A.T
        for row, Y in enumerate(K_basis):
            B_K[row, col] = np.sum(LX * Y)
            
    return B_S, B_K, S_basis, K_basis

B_S, B_K, S_basis, K_basis = lyap_op_matrices(A)
u_S, s_S, vt_S = np.linalg.svd(B_S)
u_K, s_K, vt_K = np.linalg.svd(B_K)

K_opt = sum(vt_K[0, idx] * K_basis[idx] for idx in range(len(K_basis)))
Y_opt = sum(u_K[:, 0][idx] * K_basis[idx] for idx in range(len(K_basis)))

print("Check L_A(K_opt) - s_K[0]*Y_opt norm:", np.linalg.norm(A @ K_opt + K_opt @ A.T - s_K[0] * Y_opt))
print("Check L_{A^T}(Y_opt) - s_K[0]*K_opt norm:", np.linalg.norm(A.T @ Y_opt + Y_opt @ A - s_K[0] * K_opt))

print("Singular values of K_opt:", np.linalg.svd(K_opt, compute_uv=False))
print("Singular values of Y_opt:", np.linalg.svd(Y_opt, compute_uv=False))

_, _, vh_K = np.linalg.svd(K_opt)
ker_K = vh_K[-1]
_, _, vh_Y = np.linalg.svd(Y_opt)
ker_Y = vh_Y[-1]
print("Kernel vector of K_opt:", np.round(ker_K, 6))
print("Kernel vector of Y_opt:", np.round(ker_Y, 6))
print("Angle between ker_K and ker_Y (cos theta):", np.abs(np.dot(ker_K, ker_Y)))

# Let's check what happens if we restrict A to the 6D support of K_opt!
# Wait: let Q be an orthogonal matrix whose first 6 columns span range(K_opt) and 7th column is ker_K.
Q = vh_K.T # columns are right singular vectors of K_opt; last column is ker_K
A_Q = Q.T @ A @ Q
K_Q = Q.T @ K_opt @ Q
Y_Q = Q.T @ Y_opt @ Q
print("\nIn basis Q where K_Q is supported on first 6 coords:")
print("Last row/col of K_Q norm:", np.linalg.norm(K_Q[6, :]), np.linalg.norm(K_Q[:, 6]))
# In this basis, A_Q = [[B, C], [D, E]] where B is 6x6, D is 1x6.
B_6 = A_Q[:6, :6]
D_16 = A_Q[6:, :6]
K_6 = K_Q[:6, :6]
print("E_{A_Q}(K_Q) =", np.linalg.norm(A_Q @ K_Q + K_Q @ A_Q.T)**2)
print("E_{B_6}(K_6) =", np.linalg.norm(B_6 @ K_6 + K_6 @ B_6.T)**2)
print("2 ||D_16 K_6||_F^2 =", 2 * np.linalg.norm(D_16 @ K_6)**2)
print("Sum =", np.linalg.norm(B_6 @ K_6 + K_6 @ B_6.T)**2 + 2 * np.linalg.norm(D_16 @ K_6)**2)

# Now what are the symmetric and skew norms of B_6 itself (a 6x6 matrix)?!
B_S6, B_K6, _, _ = lyap_op_matrices(B_6)
print("For 6x6 submatrix B_6:")
print("||L_{B_6}|_{S_6}||^2 =", np.linalg.svd(B_S6, compute_uv=False)[0]**2)
print("||L_{B_6}|_{K_6}||^2 =", np.linalg.svd(B_K6, compute_uv=False)[0]**2)
print("E_{B_6}(K_6) =", np.linalg.norm(B_6 @ K_6 + K_6 @ B_6.T)**2)
