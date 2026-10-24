import os
import numpy as np, json
from core import *
rng=np.random.default_rng(0)
# 1. decoupling: full op in basis [Sym;Skew] is block diagonal, singular values = union
for n in [3,4,5,6,7]:
    A=rng.standard_normal((n,n)); S,Kb=bases(n)
    Bm=np.concatenate([S,Kb]).reshape(n*n,n*n)  # rows = vec (row-major) of basis
    L=np.kron(A,np.eye(n))+np.kron(np.eye(n),A)  # row-major vec: vec(AX)=(A⊗I)x, vec(XA^T)=(I⊗A)x
    M=Bm@L@Bm.T
    ms=n*(n+1)//2
    off=max(abs(M[:ms,ms:]).max(),abs(M[ms:,:ms]).max())
    LS,LK=op_mats(A)
    print(n,'offblock',off,'blockerr',abs(M[:ms,:ms]-LS).max(),abs(M[ms:,ms:]-LK).max(),
          'normL',np.linalg.norm(L,2),'max(s,k)',max(s_k(A)))
# 2. gradient check
A=rng.standard_normal((6,6)); r,g=ratio_and_grad(A); D=rng.standard_normal((6,6)); h=1e-6
print('grad', (ratio_and_grad(A+h*D)[0]-ratio_and_grad(A-h*D)[0])/(2*h), (g*D).sum())
# 3. darboux
K=rng.standard_normal((6,6)); K=K-K.T; Q,v=darboux(K); print('darboux',np.round(Q@K@Q.T,6), v, abs(Q@Q.T-np.eye(6)).max())
K=rng.standard_normal((7,7)); K=K-K.T; Q,v=darboux(K); print('darboux7',np.round(Q@K@Q.T,4))
# 4. n=7 cert (float check)
d=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'cert_n7.json')))
A7=np.array(d['A'],float); s,k=s_k(A7); print('n7 cert: s',s,'k',k,'k/s',k/s)
# 5. min formulation random test
cnt={}
for n in [2,3,4,5,6]:
    v=0
    for t in range(2000):
        A=rng.standard_normal((n,n)); sm,km=s_k_min(A)
        if km<sm-1e-12: v+=1
    cnt[n]=v
print('min-formulation: #A with kmin<smin out of 2000:',cnt)
