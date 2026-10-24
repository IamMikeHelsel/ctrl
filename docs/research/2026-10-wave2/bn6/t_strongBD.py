"""'Strong-BD' test: is ||L_A K|| <= ||L_A on Sym ∩ comm(K^2)|| * ||K|| for ALL skew K (not just the top one)?
K = diag(J, bJ, cJ) (fixed frame), A free. Exact replica of the first exploratory run."""
import numpy as np
from scipy.optimize import minimize
from gap import blkdiag, J, bd_basis, s_restricted
from core import lyap
from core import s_k
rng=np.random.default_rng(3); B=bd_basis()
def ratio(x):
    A=x[:36].reshape(6,6); K=blkdiag(J,x[36]*J,x[37]*J)
    return s_restricted(A,B)**2*np.sum(K**2)/np.sum(lyap(A,K)**2)
worst=9
for t in range(20000):
    x=np.concatenate([rng.standard_normal(36),rng.uniform(-1,1,2)]); worst=min(worst,ratio(x))
print('random min',worst)
for t in range(3):
    x=np.concatenate([rng.standard_normal(36),rng.uniform(0.2,1,2)])
    r=minimize(ratio,x,method='Nelder-Mead',options={'maxiter':20000,'adaptive':True}); r=minimize(ratio,r.x,method='L-BFGS-B')
    A=r.x[:36].reshape(6,6); s,k=s_k(A)
    print(t,'min ratio',r.fun,'moduli (1,|b|,|c|)=',np.round(np.abs(r.x[36:]),4),' (this K is not the top skew vector: k/s of A =',round(k/s,4),')')
