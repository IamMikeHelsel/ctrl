import numpy as np

# Let's check which inner products <M, L_A(S)>_F are independent of H!
# Since A = (H + Y/2) K^{-1}, we have:
# L_A(S) = (H + Y/2) K^{-1} S - S K^{-1} (H - Y/2)
#        = (H K^{-1} S - S K^{-1} H) + (1/2)(Y K^{-1} S + S K^{-1} Y).
# Now take the Frobenius inner product with ANY symmetric matrix M (M^T = M):
# <M, H K^{-1} S - S K^{-1} H>_F = tr(M (H K^{-1} S - S K^{-1} H))
# = tr((K^{-1} S M - M S K^{-1}) H).
# When does the symmetric part of (K^{-1} S M - M S K^{-1}) vanish?
# Note that (K^{-1} S M - M S K^{-1})^T = -M S K^{-1} + K^{-1} S M = K^{-1} S M - M S K^{-1} IS ALREADY SYMMETRIC whenever M S = S M!
# Wait: even simpler! What if K^{-1} S M - M S K^{-1} = 0?!
# That happens whenever S M = K W for some W that commutes with K, OR simply:
# S M = c I_6 (or S M commutes with K)!
# In particular, choose M = S^{-1} (for ANY invertible symmetric matrix S)!
# WAIT A SECOND!
# If M = S^{-1} (where S is ANY invertible symmetric matrix), then S M = M S = I_6!
# Then K^{-1} S M - M S K^{-1} = K^{-1} - K^{-1} = 0 IDENTICALLY FOR EVERY H!
# Let's check that!
# For ANY invertible symmetric matrix S and ANY H = H^T:
# tr(S^{-1} (H K^{-1} S - S K^{-1} H)) = tr(S^{-1} H K^{-1} S) - tr(K^{-1} H) = tr(H K^{-1}) - tr(K^{-1} H) = 0!
# AND WHAT IS tr(S^{-1} L_A(S))?!
# tr(S^{-1} L_A(S)) = tr(S^{-1} (A S + S A^T)) = tr(A) + tr(A^T) = 2 tr(A) = tr(Y K^{-1})!
# Wait: what if S M is NOT just I_6, what if we use the equation (K Y) H - H (Y K) = RHS?!

# Let's check! Since H satisfies (K Y) H - H (Y K) = RHS,
# for ANY matrix X of the form (K Y) Z - Z (Y K) with Z skew-symmetric (Wait: let's check transpose of (K Y) Z - Z (Y K)):
# If Z^T = -Z (Z in K_6), then:
# ((K Y) Z - Z (Y K))^T = -Z (Y K) + (K Y) Z = (K Y) Z - Z (Y K), which is SYMMETRIC!
# And for any Z in K_6:
# tr(((K Y) Z - Z (Y K)) H) = tr(Z (H K Y - Y K H)) = -tr(Z ((K Y) H - H (Y K))) = -tr(Z * RHS) !
# WHICH IS ALSO COMPLETELY INDEPENDENT OF Which SOLUTION H WE PICK!

# WAIT A SECOND! STOP AND READ THAT AGAIN!
# Let's verify this!
M1 = np.random.randn(6, 6); K = M1 - M1.T
M2 = np.random.randn(6, 6); Y = M2 - M2.T
# Make (K, Y) compatible:
from test_subproblem import make_K, solve_pair
K = make_K(0.6, 0.35, np.sqrt(0.5 - 0.6**2 - 0.35**2))
M = np.random.randn(6, 6); M = M + M.T
_, U = np.linalg.eigh(M)
Q = U @ np.diag([1, 1, 1, -1, -1, -1]) @ U.T
Y = Q @ K @ Q
H0, H_null, _, _ = solve_pair(K, Y)
Kinv = np.linalg.inv(K)
RHS = K @ K @ K - 0.5 * (Y @ Y @ K + K @ Y @ Y)

Z = np.random.randn(6, 6); Z = Z - Z.T
Sym_Z = (K @ Y) @ Z - Z @ (Y @ K)
print("Is Sym_Z symmetric?", np.linalg.norm(Sym_Z - Sym_Z.T))

for _ in range(3):
    z = np.random.randn(len(H_null))
    H = H0 + sum(z[k] * H_null[k] for k in range(len(H_null)))
    print("tr(Sym_Z H) =", np.trace(Sym_Z @ H), "-tr(Z RHS) =", -np.trace(Z @ RHS))
