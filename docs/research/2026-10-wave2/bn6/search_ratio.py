"""Multistart local maximisation of r(A)=k(A)^2/s(A)^2 (L-BFGS on exact top-singular gradients)."""
import numpy as np, sys, time, json
from multiprocessing import Pool
from scipy.optimize import minimize
from core import ratio_and_grad, rand_A, s_k

KINDS=['gauss','sparse','nilp','cauchy','lowrank']

def f(x,n):
    A=x.reshape(n,n); A=A/np.linalg.norm(A)
    r,g=ratio_and_grad(A)
    # chain rule through normalisation (r scale invariant -> g already orthogonal to A)
    return -r, -g.ravel()/np.linalg.norm(x)

def run(args):
    n,seed=args
    rng=np.random.default_rng(seed)
    kind=KINDS[seed%len(KINDS)]
    A=rand_A(n,rng,kind)
    x0=(A/np.linalg.norm(A)).ravel()
    res=minimize(f,x0,args=(n,),jac=True,method='L-BFGS-B',options={'maxiter':3000,'gtol':1e-12,'ftol':1e-15})
    A=res.x.reshape(n,n); A/=np.linalg.norm(A)
    s,k=s_k(A)
    return (k/s, seed, kind, A.tolist())

if __name__=='__main__':
    n=int(sys.argv[1]); N=int(sys.argv[2]); off=int(sys.argv[3]) if len(sys.argv)>3 else 0
    t=time.time()
    with Pool(4) as p:
        out=p.map(run,[(n,off+i) for i in range(N)],chunksize=8)
    out.sort(key=lambda z:-z[0])
    vals=np.array([o[0] for o in out])
    print(f'n={n} starts={N} time={time.time()-t:.0f}s max k/s={vals.max():.12f} #>1: {(vals>1+1e-9).sum()} '
          f'quantiles(50,90,99)={np.quantile(vals,[.5,.9,.99])}')
    for kd in KINDS:
        vv=[o[0] for o in out if o[2]==kd]; print('  ',kd,max(vv))
    json.dump(out[:20],open(f'best_ratio_n{n}_{off}.json','w'))
