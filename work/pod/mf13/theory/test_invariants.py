import numpy as np

# Let's check what happens when we evaluate E_A(S) for A = (H + Y/2) K^{-1}!
# Wait: for A = (H + Y/2) K^{-1}, let's express L_A(X) = A X + X A^T in terms of H, K, Y!
# Even better: let's look at test symmetric matrices S!
# What happens if we choose S = I_6 (or a symmetric matrix S that commutes with something, or S related to K, Y)?
# Wait: if S = I_6, then ||I_6||_F^2 = 6, and L_A(I_6) = A + A^T.
# What is tr(A)?
# From A K + K A^T = Y, multiply by K^{-1}:
# A + K A^T K^{-1} = Y K^{-1}.
# Take the trace:
# tr(A) + tr(K A^T K^{-1}) = tr(Y K^{-1})
# => 2 tr(A) = tr(Y K^{-1})!
# Wait: what is tr(Y K^{-1})?
# Let's check! Y and K^{-1} are skew-symmetric, so tr(Y K^{-1}) doesn't have to be zero!
# Wait: from A = (H + Y/2) K^{-1}, since H is symmetric and K^{-1} is skew-symmetric,
# tr(H K^{-1}) = 0!
# Therefore: FOR ANY SOLUTION H of the coupled equations for (K, Y),
# tr(A) = (1/2) tr(Y K^{-1}) IS INDEPENDENT OF H!

# WAIT A SECOND! Is anything else independent of H?!
# Let's check! A = H K^{-1} + (1/2) Y K^{-1}.
# Let's check tr(A M) for ANY symmetric matrix M!
# Wait: if S is symmetric, what is L_A(S) = A S + S A^T?
# Can we find projections of L_A(S) that are INDEPENDENT of H, or where H is constrained by (K Y) H - H (Y K) = RHS?!

M1 = np.random.randn(6, 6); K = M1 - M1.T
M2 = np.random.randn(6, 6); Y = M2 - M2.T
H = np.random.randn(6, 6); H = H + H.T
Kinv = np.linalg.inv(K)
A = (H + 0.5 * Y) @ Kinv
print("2 tr(A) =", 2 * np.trace(A), "tr(Y K^{-1}) =", np.trace(Y @ Kinv))
