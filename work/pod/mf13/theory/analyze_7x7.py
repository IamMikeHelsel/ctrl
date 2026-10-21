import numpy as np
from fractions import Fraction

# 7x7 counterexample from Kressner & Vandereycken (arXiv:2608.20875)
A = np.array([
    [0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0],
    [6, -5, -13, 0, 0, 0, 0],
    [-14, -18, 0, 0, 0, 0, 0],
    [12, -12, 11, 0, 0, 0, 0],
    [0, 0, 0, -6, 0, -14, 0],
    [0, 0, 0, 6, -18, 0, 0]
], dtype=float)

K_int = np.array([
    [0, 4, -9, 41, 71, 4, 6],
    [-4, 0, -11, -59, 105, -12, 3],
    [9, 11, 0, 59, -10, 36, -8],
    [-41, 59, -59, 0, 9, 0, 2],
    [-71, -105, 10, -9, 0, -15, 0],
    [-4, 12, -36, 0, 15, 0, 4],
    [-6, -3, 8, -2, 0, -4, 0]
], dtype=float)

print("--- 7x7 Matrix A analysis ---")
print("Rank of A:", np.linalg.matrix_rank(A))
print("Eigenvalues of A:", np.linalg.eigvals(A))
print("Singular values of A:", np.linalg.svd(A, compute_uv=False))

print("\n--- Integer witness K_int analysis ---")
print("Rank of K_int:", np.linalg.matrix_rank(K_int))
print("Singular values of K_int:", np.linalg.svd(K_int, compute_uv=False))
Y_int = A @ K_int + K_int @ A.T
print("Singular values of L_A(K_int):", np.linalg.svd(Y_int, compute_uv=False))

# Exact operator matrices B_S and B_K
def lyap_op_matrices(A):
    n = A.shape[0]
    # Orthonormal basis for S_n and K_n
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
    
    def apply_L(X):
        return A @ X + X @ A.T
    
    B_S = np.zeros((len(S_basis), len(S_basis)))
    for col, X in enumerate(S_basis):
        LX = apply_L(X)
        for row, Y in enumerate(S_basis):
            B_S[row, col] = np.sum(LX * Y)
            
    B_K = np.zeros((len(K_basis), len(K_basis)))
    for col, X in enumerate(K_basis):
        LX = apply_L(X)
        for row, Y in enumerate(K_basis):
            B_K[row, col] = np.sum(LX * Y)
            
    return B_S, B_K, S_basis, K_basis

B_S, B_K, S_basis, K_basis = lyap_op_matrices(A)
u_S, s_S, vt_S = np.linalg.svd(B_S)
u_K, s_K, vt_K = np.linalg.svd(B_K)

print("\n--- Exact singular values of L_A on S_7 and K_7 ---")
print("Top 5 singular values squared on S_7:", s_S[:5]**2)
print("Top 5 singular values squared on K_7:", s_K[:5]**2)

# Reconstruct exact top skew singular vectors K_opt and Y_opt
K_opt = sum(vt_K[0, idx] * K_basis[idx] for idx in range(len(K_basis)))
Y_opt = sum(u_K[0, idx] * K_basis[idx] for idx in range(len(K_basis)))

print("\nSingular values of K_opt:", np.linalg.svd(K_opt, compute_uv=False))
print("Singular values of Y_opt:", np.linalg.svd(Y_opt, compute_uv=False))

# Check kernel of K_opt and Y_opt
_, _, vh_K = np.linalg.svd(K_opt)
ker_K = vh_K[-1]
_, _, vh_Y = np.linalg.svd(Y_opt)
ker_Y = vh_Y[-1]
print("Kernel vector of K_opt:", np.round(ker_K, 6))
print("Kernel vector of Y_opt:", np.round(ker_Y, 6))
print("Inner product of ker_K and ker_Y:", np.abs(np.dot(ker_K, ker_Y)))

# Also check S_opt
S_opt = sum(vt_S[0, idx] * S_basis[idx] for idx in range(len(S_basis)))
print("Eigenvalues of S_opt:", np.linalg.eigvalsh(S_opt))
