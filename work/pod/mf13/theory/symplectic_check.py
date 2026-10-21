import numpy as np

# Let's analyze the compatibility of (K, Y) in dimension n=6!
# Suppose K, Y in K_6 are invertible skew-symmetric matrices with ||K||_F = ||Y||_F.
# Let's check: what are the eigenvalues of Y K?
# Since K is invertible and skew-symmetric, K = -K^T.
# Actually, let's check if the eigenvalues of Y K come in pairs!
# For any two skew-symmetric matrices Y, K:
# (Y K)^T = K^T Y^T = (-K)(-Y) = K Y.
# And K^{-1} (Y K) K = K Y = (Y K)^T.
# Even better: on each generalized eigenspace of Y K, K induces a skew-symmetric bilinear form!
# Wait: for any x, y, <x, K Y K y> = <K^T x, Y K y> = -<K x, Y K y> = -<Y^T K x, K y> = <Y K x, K y>.
# That means with respect to the nondegenerate skew-symmetric form omega(x, y) = x^T K^{-1} y,
# the operator T = Y K satisfies:
# omega(T x, y) = (Y K x)^T K^{-1} y = x^T K^T Y^T K^{-1} y = x^T K Y K^{-1} y = x^T K^{-1} (Y K y) = omega(x, T y) !
# WAIT A SECOND!
# T = Y K is SELF-ADJOINT with respect to the symplectic form omega(x, y) = x^T K^{-1} y (or omega'(x, y) = x^T Y y)!
# In a symplectic vector space, an operator T that is symplectic-self-adjoint (omega(Tx, y) = omega(x, Ty), i.e. K^{-1} T = T^T K^{-1})
# has EVERY eigenvalue with EVEN multiplicity! (In fact, every Jordan block of T occurs in duplicate pairs!)

# Let's verify this numerically on random 6x6 skew-symmetric matrices Y, K!
for _ in range(3):
    M1 = np.random.randn(6, 6); K = M1 - M1.T
    M2 = np.random.randn(6, 6); Y = M2 - M2.T
    evals = np.linalg.eigvals(Y @ K)
    print("Eigenvalues of random Y @ K:", np.sort_complex(evals))
