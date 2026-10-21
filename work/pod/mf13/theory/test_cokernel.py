import numpy as np

# Let's check the linear operator Phi(H) = (K Y) H - H (Y K) from S_6 to K_6
# and the condition for RHS = K^3 - (Y^2 K + K Y^2)/2 to be in range(Phi)!

def test_generic_pair():
    # Generate random invertible skew-symmetric K, Y
    M1 = np.random.randn(6, 6); K = M1 - M1.T
    M2 = np.random.randn(6, 6); Y = M2 - M2.T
    
    # Basis of S_6 (dim 21) and K_6 (dim 15)
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
            
    # Matrix of Phi: S_6 -> K_6
    Phi = np.zeros((15, 21))
    KY = K @ Y
    YK = Y @ K
    for col, H in enumerate(S_basis):
        out = KY @ H - H @ YK
        for row, W in enumerate(K_basis):
            Phi[row, col] = np.sum(out * W)
            
    print("Rank of Phi on random pair:", np.linalg.matrix_rank(Phi))
    # What is the left kernel (cokernel) of Phi in K_6?
    # For W in K_6, <W, (K Y) H - H (Y K)>_F = -tr(W ((K Y) H - H (Y K)))
    # = -tr((W K Y - Y K W) H).
    # Note that (W K Y - Y K W)^T = Y K W - W K Y = -(W K Y - Y K W)... wait:
    # Let's check transpose of W K Y - Y K W when W, K, Y in K_6:
    # (W K Y)^T = Y^T K^T W^T = (-Y)(-K)(-W) = -Y K W!
    # So (W K Y - Y K W)^T = -Y K W + W K Y = W K Y - Y K W, which is SYMMETRIC!
    # Therefore, W in K_6 is orthogonal to range(Phi) iff W K Y - Y K W = 0!
    # Since K is invertible, multiply on left or right by K:
    # (W K)(Y K) = (Y K)(W K)!
    # That is: W K commutes with T = Y K!
    
    # Wait: what matrices of the form W K (with W in K_6) commute with T = Y K?
    # Note that M = W K satisfies K^{-1} M = W, which is skew-symmetric, so (K^{-1} M)^T = -K^{-1} M,
    # i.e. M^T K^{-1} = K^{-1} M, which is the EXACT SAME symplectic self-adjoint condition as T = Y K!
    # And dynamically, I, T, T^2 are all of the form W K with W in K_6!
    # Specifically, for j=0, 1, 2:
    # T^j = (Y K)^j = W_j K where W_j = (Y K)^j K^{-1} = Y (K Y)^{j-1} is skew-symmetric!
    
    u, s, vt = np.linalg.svd(Phi)
    cokernel = u[:, 12:] # 3 vectors in K_6
    # Check if cokernel is spanned by W_0 = K^{-1}, W_1 = Y, W_2 = Y K Y!
    W0 = np.linalg.inv(K)
    W1 = Y
    W2 = Y @ K @ Y
    Span_W = np.zeros((15, 3))
    for col, W in enumerate([W0, W1, W2]):
        for row, B in enumerate(K_basis):
            Span_W[row, col] = np.sum(W * B)
    print("Rank of [W0, W1, W2]:", np.linalg.matrix_rank(Span_W))
    print("Phi^T @ Span_W norm:", np.linalg.norm(Phi.T @ Span_W))

    # Now let's check <W_j, RHS>_F for j = 0, 1, 2!
    # RHS = K^3 - (Y^2 K + K Y^2)/2.
    # For W in K_6, <W, RHS>_F = -tr(W (K^3 - (Y^2 K + K Y^2)/2))
    # Since W = (Y K)^j K^{-1} and W commutes with Y K (Wait: W K = T^j commutes with K):
    # Wait: tr(W K^3) = tr(T^j K^2), and tr(W (Y^2 K + K Y^2)/2) = tr(T^j Y^2)!
    # Because W Y^2 K = T^j K^{-1} Y^2 K, and W K Y^2 = T^j Y^2!
    # Wait: is tr(W (Y^2 K + K Y^2)/2) equal to tr(T^j Y^2)?
    # Let's check!
    RHS = K @ K @ K - 0.5 * (Y @ Y @ K + K @ Y @ Y)
    for j, W in enumerate([W0, W1, W2]):
        inner1 = -np.trace(W @ RHS)
        inner2 = np.trace(np.linalg.matrix_power(YK, j) @ (K @ K - Y @ Y))
        # Wait: let's check the relation between -tr(W @ RHS) and tr((YK)^j (K^2 - Y^2))!
        print(f"j={j}: -tr(W_j RHS) = {inner1:.6f}, tr((YK)^j (K^2 - Y^2)) = {inner2:.6f}")

test_generic_pair()
