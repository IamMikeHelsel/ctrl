import numpy as np
from evalf import *
from scipy.stats import ortho_group
rng = np.random.default_rng(0)
K = make_K(0.5, 0.4, np.sqrt(0.5 - 0.25 - 0.16))
print("a,b,c", 0.5, 0.4, np.sqrt(0.09))
for kind in ('sym_involution', 'general_orth', 'skew_complex'):
    for t in range(4):
        U = ortho_group.rvs(6, random_state=rng)
        if kind == 'sym_involution':
            k = rng.integers(1, 6)
            Q = U @ np.diag([1.]*k + [-1.]*(6-k)) @ U.T
        elif kind == 'general_orth':
            Q = U
        else:
            Jb = np.kron(np.eye(3), J2)
            Q = U @ Jb @ U.T   # skew orthogonal Q^2=-I
        for sign in (1, -1):
            Y = sign * Q @ K @ Q.T
            m = moments(K, Y)
            out = f_of_pair(K, Y) if np.linalg.norm(m) < 1e-9 else dict(f=np.nan, resid=np.nan, nullity=-1)
            print(kind, sign, "moments", np.round(np.abs(m).max(), 12), "f", out['f'], "nullity", out['nullity'])
