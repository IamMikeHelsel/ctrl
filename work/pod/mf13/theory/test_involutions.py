import numpy as np
from scipy.optimize import minimize

# Let's construct a generator of compatible full-rank pairs (K, Y) in n=6!
# Suppose K is in canonical form: K = diag(a J, b J, c J), with a^2 + b^2 + c^2 = 1/2 (so ||K||_F^2 = 1).
# How to generate Y in K_6 such that tr((Y K)^j (Y^2 - K^2)) = 0 for j = 0, 1, 2?
# Wait: for a given K and a random direction Y0 in K_6:
# Notice that j=0 is ||Y||_F^2 = ||K||_F^2 = 1 (quadratic in Y).
# j=1 is tr(Y K Y^2 - Y K^3) = 0 -> tr(Y^3 K) = tr(Y K^3)! (cubic vs linear in Y!)
#Wait: if we replace Y by t Y, then tr((tY)^3 K) = t^3 tr(Y^3 K) and tr((tY) K^3) = t tr(Y K^3)!
# Wait: if we fix ||Y||_F^2 = ||K||_F^2, then j=1 and j=2 are 2 scalar equations on the 14-dimensional sphere of unit skew matrices Y!
# Even better: what if Y = Q K Q^T for some Q in O(6)?
# WAIT A SECOND!
# If Y and K are ISOSPECTRAL (i.e. Y = Q K Q^T for some Q in O(6)), what happens to the trace moments?!
# Let's check!
# j = 0: tr(Y^2 - K^2) = 0 AUTOMATICALLY because Y and K are isospectral!
# j = 1: tr(Y K (Y^2 - K^2)) = tr(Y^3 K) - tr(Y K^3).
# If Y = Q K Q^T, then tr(Y^3 K) = tr(Q K^3 Q^T K) = tr(K^3 Q^T K Q), whereas tr(Y K^3) = tr(Q K Q^T K^3).
# By cyclic invariance of trace:
# tr(Y^3 K) = tr((Y^3 K)^T) = tr((-K)(-Y^3)) = tr(K Y^3).
# Wait: for general Y = Q K Q^T, is tr(Y^3 K) = tr(Y K^3)?
# If Q^T = Q (symmetric orthogonal) or Q^2 = I, then Q K Q^T = Q^T K Q, so tr(Q K^3 Q^T K) = tr(K^3 Q^T K Q) = tr(K^3 Y) = tr(Y K^3)!
# WAIT A SECOND!
# If Q is ANY orthogonal matrix such that Y = Q K Q^T, when does j=1 and j=2 hold automatically?!

J2 = np.array([[0., 1.], [-1., 0.]])
def make_K(a, b, c):
    K = np.zeros((6, 6))
    K[0:2, 0:2] = a * J2
    K[2:4, 2:4] = b * J2
    K[4:6, 4:6] = c * J2
    return K

K = make_K(0.6, 0.35, np.sqrt(0.5 - 0.6**2 - 0.35**2))

# Test if Q is symmetric orthogonal (involution Q = Q^T, Q^2 = I):
M = np.random.randn(6, 6); M = M + M.T
_, U = np.linalg.eigh(M)
D = np.diag([1, 1, 1, -1, -1, -1])
Q = U @ D @ U.T # symmetric orthogonal!
Y = Q @ K @ Q.T

for j in range(5):
    val = np.trace(np.linalg.matrix_power(Y @ K, j) @ (Y @ Y - K @ K))
    print(f"Symmetric orthogonal Q, j={j}: moment = {val:.2e}")

# Wait! What if Y is obtained from K by ANY orthogonal involution Q (or more generally, when is (K, Y) exchangeable by an orthogonal/symplectic map)?
# Wait: if Q = Q^T in O(6) and Y = Q K Q, then:
# Q Y Q = K and Q K Q = Y!
# That means conjugation by Q SWAPS K and Y!
# And under conjugation by Q:
# Q (Y K) Q = K Y = (Y K)^T!
# Q (Y^2 - K^2) Q = K^2 - Y^2 = -(Y^2 - K^2)!
# Wait: then tr((Y K)^j (Y^2 - K^2)) = tr(Q (Y K)^j (Y^2 - K^2) Q) = tr((K Y)^j (K^2 - Y^2))
# = tr(((Y K)^j)^T (K^2 - Y^2)) = tr((K^2 - Y^2) (Y K)^j) = -tr((Y K)^j (Y^2 - K^2))!
# SO EVERY SINGLE TRACE MOMENT j >= 0 VANISHES IDENTICALLY WHENEVER (K, Y) ARE RELATED BY AN ORTHOGONAL INVOLUTION (OR ANY MAP SWAPPING K AND Y)!
