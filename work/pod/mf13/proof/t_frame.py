import numpy as np
from core import *
from ssclass import frame
rng=np.random.default_rng(0)
for t in range(5):
    K = skew_of(rng.standard_normal(15))
    if t>=2:
        A=rng.standard_normal((6,4)); K = A@make_K(1,0.3)@A.T if t<4 else A@make_K(1,1)@A.T
    F,w = frame(K); D = F.T@K@F
    print(np.round(w,4), np.linalg.norm(D - make_K(*w)), np.linalg.norm(F.T@F-np.eye(6)))
