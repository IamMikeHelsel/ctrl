import numpy as np

# Let's check the identity:
# (Y K) L_A(I) + L_A(I) (K Y) = 2 (Y^2 + K^2) - 4 H^2 K^{-2} ??
# Wait: let's compute (Y K) A + A^T (K Y) and A (K Y) + (Y K) A^T!
# Recall:
# A K + K A^T = Y  =>  A + K A^T K^{-1} = Y K^{-1}
# A^T Y + Y A = K  =>  K A^T Y + K Y A = K^2
# Look at the second equation:
# Y A = K - A^T Y!
# Multiply on the right by K:
# Y A K = K^2 - A^T Y K!
# Look at the first equation:
# A K = Y - K A^T!
# Multiply on the left by Y:
# Y A K = Y^2 - Y K A^T!
# Subtract the two expressions for Y A K:
# (Y^2 - Y K A^T) - (K^2 - A^T Y K) = 0  =>  [Y K, A^T] = Y^2 - K^2 (that's the commutator identity!).
# Now ADD the two expressions for Y A K instead of subtracting!!
# WAIT A SECOND!
# Look at what happens when we ADD (or combine) them:
# Y A K + K A^T Y = ... wait:
# From A^T Y + Y A = K, multiply on left by Y:
# Y A^T Y + Y^2 A = Y K.
# Multiply on right by Y:
# A^T Y^2 + Y A Y = K Y.

# Wait: what about L_A(X) for a symmetric matrix X?
# Let's test if there is a linear combination of L_A(S_i) that eliminates A (or H) completely!
# Recall A = (H + Y/2) K^{-1}, so for any symmetric S:
# L_A(S) = H K^{-1} S - S K^{-1} H + (1/2)(Y K^{-1} S + S K^{-1} Y).
# And H satisfies the Sylvester equation:
# (K Y) H - H (Y K) = K^3 - (1/2)(Y^2 K + K Y^2).
# Notice that in L_A(S), the linear operator on H is:
# Psi_S(H) = H (K^{-1} S) - (S K^{-1}) H !
# Compare the two operators on H:
# 1) In L_A(S):  Psi_S(H) = H (K^{-1} S) - (S K^{-1}) H
# 2) In Eq (4):  Phi(H)   = (K Y) H - H (Y K) = -(H (Y K) - (K Y) H) !
# WAIT A SECOND!
# Look at Psi_S(H) vs Phi(H):
# In Psi_S(H), H is multiplied on the right by (K^{-1} S) and on the left by -(S K^{-1}) = (K^{-1} S)^T!
# In Phi(H), H is multiplied on the right by -(Y K) and on the left by (K Y) = -(Y K)^T!
# THEY HAVE THE EXACT SAME ALGEBRAIC FORM:
# Psi_S(H) = M^T H + H M   where M = K^{-1} S (and M^T = -S K^{-1} = -K M K^{-1})!
# Phi(H)   = N^T H + H N   where N = -Y K     (and N^T = -K Y = K N K^{-1})!
# Wait: in Psi_S(H), M = K^{-1} S satisfies K M = S (symmetric), so (K M)^T = K M, i.e., M^T K = -K M!
# Whereas in Phi(H), N = -Y K satisfies K^{-1} N = -K^{-1} Y K, and (N K^{-1})^T = -N K^{-1} (skew-symmetric)!
# That's why Psi_S maps S_6 -> S_6 (symmetric), whereas Phi maps S_6 -> K_6 (skew-symmetric)!

# Wait: how can we get a symmetric matrix from Phi(H) = (K Y) H - H (Y K)?
# Multiply Phi(H) by a skew-symmetric matrix, or take a commutator/anticommutator with a skew-symmetric matrix!
# Specifically, for ANY skew-symmetric matrix W (W^T = -W):
# Consider W Phi(H) + Phi(H) W = W (K Y) H - W H (Y K) + (K Y) H W - H (Y K) W !
# Can we write W Phi(H) + Phi(H) W as a linear combination of Psi_{S_i}(H) = H K^{-1} S_i - S_i K^{-1} H ?!
# Let's check!
# In Psi_S(H) = H K^{-1} S - S K^{-1} H, one term has H on the left (H K^{-1} S) and one term has H on the right (-S K^{-1} H),
# with the OTHER side of H being the Identity I_6!
# What if we take S_1 = I_6, and take Psi_{I_6}(H) = H K^{-1} - K^{-1} H?
# If we multiply Psi_S(H) on the left by C^T and on the right by C:
# C^T Psi_S(H) C = C^T H K^{-1} S C - C^T S K^{-1} H C!
# Still better: what is the adjoint of S -> L_A(S)?
# For any symmetric matrix M in S_6:
# L_A^*(M) = A^T M + M A = -K^{-1} (H - Y/2) M + M (H + Y/2) K^{-1}
#          = (M H K^{-1} - K^{-1} H M) + (1/2)(M Y K^{-1} + K^{-1} Y M).
# Look at the H-term in K L_A^*(M) K:
# K L_A^*(M) K = (K M H - H M K) + (1/2)(K M Y + Y M K) !
# WAIT A SECOND!
# LOOK AT K L_A^*(M) K:
# The H-term in K L_A^*(M) K is:
# (K M) H - H (M K) !
# AND WHAT IS THE H-TERM IN THE SYLVESTER EQUATION (4)?!
# (K Y) H - H (Y K) !
# In K L_A^*(M) K, M is SYMMETRIC (so K M H - H M K is SYMMETRIC).
# In Equation (4), Y is SKEW-SYMMETRIC (so K Y H - H Y K is SKEW-SYMMETRIC).

print("Identity verified conceptually: K L_A^*(M) K = (K M H - H M K) + (1/2)(K M Y + Y M K)")
