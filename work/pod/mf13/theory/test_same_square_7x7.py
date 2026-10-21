import numpy as np

# From analyze_7x7_part2, let's check max_{S^2 = -K_6^2} E_{B_6}(S)
from analyze_7x7_part2 import B_6, K_6, D_16, A_Q, K_Q

# Put K_6 into canonical form diag(a J, b J, c J)
# Real Schur decomposition or SVD of K_6
# Since K_6 is 6x6 skew-symmetric, K_6^2 is symmetric negative definite with double eigenvalues -a^2, -b^2, -c^2
evals, evecs = np.linalg.eigh(-K_6 @ K_6)
# Sort descending
idx = np.argsort(evals)[::-1]
evals = evals[idx]
evecs = evecs[:, idx]

# Construct orthogonal basis U where U^T K_6 U = diag(a J, b J, c J)
U = np.zeros((6, 6))
svals = []
for b in range(3):
    u1 = evecs[:, 2*b]
    u1 = u1 / np.linalg.norm(u1)
    v = K_6 @ u1
    lam = np.linalg.norm(v)
    u2 = -v / lam # so K_6 u1 = -lam u2, K_6 u2 = lam u1 -> [0, lam; -lam, 0]
    U[:, 2*b] = u1
    U[:, 2*b+1] = u2
    svals.append(lam)

print("Check U orthogonal:", np.linalg.norm(U.T @ U - np.eye(6)))
K_can = U.T @ K_6 @ U
print("K_can:\n", np.round(K_can, 4))
B_can = U.T @ B_6 @ U

# A general symmetric S with S^2 = -K_can^2 (assuming distinct a, b, c)
# must commute with K_can^2, so S is block-diagonal with 2x2 blocks lambda_i * Q_i,
# where Q_i^T = Q_i and Q_i^2 = I_2.
# Wait: a 2x2 symmetric matrix with Q_i^2 = I_2 is either +/- I_2 or a reflection R(theta_i)!
# Let's check all combinations of (+/- I_2 or R(theta_i)) on the 3 blocks!
def R_mat(theta):
    return np.array([[np.cos(theta), np.sin(theta)], [np.sin(theta), -np.cos(theta)]])

# Maximize E_{B_can}(S) over theta_1, theta_2, theta_3
from scipy.optimize import minimize

best_val = -1e9
for p in range(50):
    x0 = np.random.uniform(0, 2*np.pi, 3)
    def neg_E(thetas):
        S = np.zeros((6, 6))
        for i in range(3):
            S[2*i:2*i+2, 2*i:2*i+2] = svals[i] * R_mat(thetas[i])
        LS = B_can @ S + S @ B_can.T
        return -np.sum(LS * LS)
    res = minimize(neg_E, x0)
    if -res.fun > best_val:
        best_val = -res.fun
        best_thetas = res.x

print("E_{B_6}(K_6) =", np.linalg.norm(B_can @ K_can + K_can @ B_can.T)**2)
print("Max E_{B_6}(S) over block reflections S^2 = -K_6^2:", best_val)

# Also check if any block is +/- I_2 instead of R(theta):
# Wait: for S^2 = -K_6^2, even if a block is +/- I_2, we can test all 3^3 combinations of (R(theta), +I, -I)
best_all = best_val
for c0 in ['R', '+I', '-I']:
    for c1 in ['R', '+I', '-I']:
        for c2 in ['R', '+I', '-I']:
            choices = [c0, c1, c2]
            def neg_E_c(thetas):
                S = np.zeros((6, 6))
                for i in range(3):
                    if choices[i] == 'R':
                        blk = R_mat(thetas[i])
                    elif choices[i] == '+I':
                        blk = np.eye(2)
                    else:
                        blk = -np.eye(2)
                    S[2*i:2*i+2, 2*i:2*i+2] = svals[i] * blk
                LS = B_can @ S + S @ B_can.T
                return -np.sum(LS * LS)
            for _ in range(10):
                res = minimize(neg_E_c, np.random.uniform(0, 2*np.pi, 3))
                if -res.fun > best_all:
                    best_all = -res.fun
                    best_choices = choices

print("Max E_{B_6}(S) over ALL S with S^2 = -K_6^2:", best_all)
print("Adding 2||D_16 K_6||^2 =", best_all + 2 * np.linalg.norm(D_16 @ K_6)**2)
print("Compare to ||L_A|_{S_7}||^2 =", 1195.59398484)
print("Compare to E_A(K_opt) =", 1196.02522370)
