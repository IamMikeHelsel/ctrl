"""E01: check the algebraic identities used in the proof sketch.
 (I1) T sym involution, TK=-KT, M=AK, Y=L_A K:  E_A(KT)-E_A(K) = tr((M+TMT)^2)
 (I2) same with H=sym(AK), Y_a=(Y-TYT)/2:  ||L_A(KT)||^2 = ||HT+TH||^2 + ||Y_a||^2
 (I3) common-T lemma: if also TY=-YT, <YT, L_A(KT)> = ||Y||^2
 (I4) dual identity: for skew Z1,Z2 and A with pair (K,Y): 2tr(A K Z1) = tr(Z1 Y), 2 tr(A Z2 Y) = tr(Z2 K)
 (I5) <U, L_A V> = 2 tr(A V U) for symmetric U,V
"""
import numpy as np
from scipy.stats import ortho_group
from core import *

rng = np.random.default_rng(1)
mx = np.zeros(6)
for t in range(200):
    A = rng.standard_normal((6, 6))
    Q = ortho_group.rvs(6, random_state=rng)
    w = rng.uniform(0.1, 1, 3)
    K = Q @ make_K(*w) @ Q.T
    th = rng.uniform(0, 2 * np.pi, 3)
    T0 = np.zeros((6, 6))
    for i in range(3):
        T0[2*i:2*i+2, 2*i:2*i+2] = [[np.cos(th[i]), np.sin(th[i])], [np.sin(th[i]), -np.cos(th[i])]]
    T = Q @ T0 @ Q.T
    Y = L(A, K); M = A @ K
    E = lambda X: np.sum(L(A, X) ** 2)
    mx[0] = max(mx[0], abs(E(K @ T) - E(K) - np.trace((M + T @ M @ T) @ (M + T @ M @ T))))
    H = (M + M.T) / 2; Ya = (Y - T @ Y @ T) / 2
    mx[1] = max(mx[1], abs(E(K @ T) - np.sum((H @ T + T @ H) ** 2) - np.sum(Ya ** 2)))
    # I3: construct Y anticommuting with T: use A' with L_A' K anticommuting? just test algebra with random skew Y' anticommuting
    Yp = skew_of(rng.standard_normal(15)); Yp = (Yp - T @ Yp @ T) / 2
    # find A' with L_A'(K) = Yp: A' = (H' + Yp/2) K^{-1}, H' random sym
    Hp = sym_of(rng.standard_normal(21)); Ap = (Hp + Yp / 2) @ np.linalg.inv(K)
    mx[2] = max(mx[2], abs(np.sum((Yp @ T) * L(Ap, K @ T)) - np.sum(Yp ** 2)) + np.linalg.norm(L(Ap, K) - Yp))
    U = sym_of(rng.standard_normal(21)); V = sym_of(rng.standard_normal(21))
    mx[4] = max(mx[4], abs(np.sum(U * L(A, V)) - 2 * np.trace(A @ V @ U)))
# I4 on a true compatible pair
for t in range(20):
    K, Y, err = random_pair(rng)
    A0, Ar, res = affine_family(K, Y)
    A = A0 + np.tensordot(rng.standard_normal(len(Ar)), Ar, axes=(0, 0))
    Z1 = skew_of(rng.standard_normal(15)); Z2 = skew_of(rng.standard_normal(15))
    mx[3] = max(mx[3], abs(2 * np.trace(A @ K @ Z1) - np.trace(Z1 @ Y)) + abs(2 * np.trace(A @ Z2 @ Y) - np.trace(Z2 @ K)), res)
print("max errors I1..I5:", mx[:5])
