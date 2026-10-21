import numpy as np

# Suppose Q = Q^T, Q^2 = I_6, and Y = Q K Q.
# Let's check what H0 = 0 gives!
# Wait: if Y = Q K Q, does H = 0 solve (K Y) H - H (Y K) = K^3 - (Y^2 K + K Y^2)/2?
# No, unless K^3 = (Y^2 K + K Y^2)/2 (which is Y^2 = K^2, i.e. Y = ± K).
# Wait: for Y = Q K Q, let's check what E_A(Q) is for ANY solution A = (H + Y/2) K^{-1}!
# Wait: Q is a SYMMETRIC matrix (Q^T = Q) with ||Q||_F^2 = 6!
# What is L_A(Q) = A Q + Q A^T?
# Wait: A K + K A^T = Y = Q K Q, and A^T Y + Y A = K => A^T Q K Q + Q K Q A = K => (Q A^T Q) K + K (Q A Q) = K!
# Look at those two equations:
# 1) (A Q) (Q K) + (Q K) (A Q)^T = Q K ... wait:
# Multiply A K + K A^T = Q K Q on the left by Q and on the right by Q:
# (Q A) K + K (A^T Q) = K!
# And the second equation is:
# (Q A^T Q) K + K (Q A Q) = K!
# Add them together!
# Let M = Q A + Q A^T Q = Q (A + A^T Q) = Q L_A(Q)!
# Then M K + K M^T = 2 K!
# Multiply by K^{-1}:
# M + K M^T K^{-1} = 2 I_6!
# Take the trace:
# 2 tr(M) = 12 => tr(M) = 6!
# Since M = Q L_A(Q) and ||Q||_F^2 = 6:
# 6 = tr(Q L_A(Q)) = <Q, L_A(Q)>_F <= ||Q||_F ||L_A(Q)||_F = sqrt(6) ||L_A(Q)||_F!
# Therefore:
# ||L_A(Q)||_F >= sqrt(6) = ||Q||_F!
# SO FOR EVERY INVOLUTIVE PAIR Y = Q K Q (WITH Q = Q^T, Q^2 = I_6),
# THE SYMMETRIC MATRIX S = Q ALWAYS HAS ||L_A(Q)||_F / ||Q||_F >= 1 = ||L_A(K)||_F / ||K||_F!

# Let's verify this theorem numerically!
from test_subproblem import make_K, solve_pair
K = make_K(0.6, 0.35, np.sqrt(0.5 - 0.6**2 - 0.35**2))
M = np.random.randn(6, 6); M = M + M.T
_, U = np.linalg.eigh(M)
Q = U @ np.diag([1, 1, 1, -1, -1, -1]) @ U.T
Y = Q @ K @ Q
H0, H_null, _, _ = solve_pair(K, Y)
Kinv = np.linalg.inv(K)
for _ in range(5):
    z = np.random.randn(len(H_null))
    H = H0 + sum(z[k] * H_null[k] for k in range(len(H_null)))
    A = (H + 0.5 * Y) @ Kinv
    LQ = A @ Q + Q @ A.T
    print("tr(Q L_A(Q)) =", np.trace(Q @ LQ), "||L_A(Q)||_F^2 / ||Q||_F^2 =", np.sum(LQ*LQ) / 6.0)
