import numpy as np
from scipy.stats import ortho_group
rng = np.random.default_rng(1)
for t in range(5):
    C = rng.standard_normal((3,3)); K = np.zeros((6,6)); K[:3,3:] = -C.T; K[3:,:3] = C
    A = np.zeros((6,6)); A[:3,:3] = rng.standard_normal((3,3)); A[3:,3:] = rng.standard_normal((3,3))
    Q = ortho_group.rvs(6, random_state=rng)           # random orthogonal change of basis
    T = Q @ np.diag([1,1,1,-1,-1,-1.]) @ Q.T
    K = Q @ K @ Q.T; A = Q @ A @ Q.T
    L = lambda X: A @ X + X @ A.T
    Y = L(K)
    Xv = K @ T; Xu = Y @ T
    print("sym:", np.linalg.norm(Xv - Xv.T), np.linalg.norm(Xu - Xu.T), " <Xu,L Xv> =", np.sum(Xu * L(Xv)), " |Y|^2 =", np.sum(Y*Y), " |L Xv| >= |Y|:", np.linalg.norm(L(Xv)), np.linalg.norm(Y))
