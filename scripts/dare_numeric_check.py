# Numeric companion: value iteration from 0 (as in riccatiIter) vs SciPy's DARE solver,
# plus checks of the Lean statements' claims on a random stabilizable example.
import numpy as np
from scipy.linalg import solve_discrete_are

rng = np.random.default_rng(0)
n, m, p = 4, 2, 2
A = rng.normal(size=(n, n)) * 0.9
B = rng.normal(size=(n, m))
C = rng.normal(size=(p, n))
Q = np.eye(n)
R = np.eye(m)
W = np.eye(n)
V = np.eye(p)


def T(P, A, B, Q, R):
    G = R + B.T @ P @ B
    K = np.linalg.solve(G, B.T @ P @ A)
    AK = A - B @ K
    return Q + K.T @ R @ K + AK.T @ P @ AK, K


P = np.zeros((n, n))
prev = None
mono = True
for k in range(500):
    Pn, K = T(P, A, B, Q, R)
    if np.min(np.linalg.eigvalsh(Pn - P)) < -1e-9:
        mono = False
    P = Pn
Ps = solve_discrete_are(A, B, Q, R)
_, K = T(P, A, B, Q, R)
print("spectral radius A        :", max(abs(np.linalg.eigvals(A))))
print("monotone iterates        :", mono)
print("|P_iter - P_scipy|       :", np.abs(P - Ps).max())
print("rho(A - B K)             :", max(abs(np.linalg.eigvals(A - B @ K))))
S = np.zeros((n, n))
for k in range(500):
    S, L = T(S, A.T, C.T, W, V)
Ss = solve_discrete_are(A.T, C.T, W, V)
L = A @ S @ C.T @ np.linalg.inv(V + C @ S @ C.T)
print("|Sigma_iter - scipy|     :", np.abs(S - Ss).max())
print("rho(A - L C)             :", max(abs(np.linalg.eigvals(A - L @ C))))
Acl = np.block([[A - B @ K, B @ K], [np.zeros((n, n)), A - L @ C]])
print("rho(LQG closed loop)     :", max(abs(np.linalg.eigvals(Acl))))
