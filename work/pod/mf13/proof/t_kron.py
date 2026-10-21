"""Independent check of k/s via Kronecker form + mpmath, for a saved A."""
import sys, numpy as np, mpmath as mp
A = np.load(sys.argv[1]); n = A.shape[0]
I = np.eye(n); Lk = np.kron(A, I) + np.kron(I, A)   # vec_row(AX + XA^T) = (A⊗I + I⊗A) vec_row(X)
Pm = np.zeros((n*n, n*n))
for i in range(n):
    for j in range(n): Pm[i*n+j, j*n+i] = 1
Ps = (np.eye(n*n) + Pm) / 2; Pk = (np.eye(n*n) - Pm) / 2
s = np.linalg.norm(Lk @ Ps, 2); k = np.linalg.norm(Lk @ Pk, 2)
print("float: s =", s, "k =", k, "k/s =", k / s)
mp.mp.dps = 40
M = mp.matrix(Lk.tolist())
def top(P):
    B = M * mp.matrix(P.tolist()); ev = mp.eigsy(B.T * B)[0]
    return mp.sqrt(max(ev))
print("mpmath k/s =", top(Pk) / top(Ps))
