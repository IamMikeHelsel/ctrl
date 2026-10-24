"""Adversarial minimisation of cBD(A) = s_BD(A)^2 / k(A)^2 (block-diagonal comparator span, Darboux frame of top skew K)."""
import os; os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, json, sys, time
from multiprocessing import Pool
from scipy.optimize import minimize
from gap import frame, s_restricted, bd_basis, diagnostics
from core import rand_A, lyap
D=os.path.dirname(os.path.abspath(__file__))

def cbd(x):
    A=x.reshape(6,6)
    A1,K1,fr,k,sv=frame(A)
    s=s_restricted(A1,bd_basis())
    return (s/k)**2

def job(seed):
    rng=np.random.default_rng(777+seed)
    kinds=['gauss','sparse','nilp','lowrank']
    A=rand_A(6,rng,kinds[seed%4]); x=A.ravel()/np.linalg.norm(A)
    best=cbd(x)
    for rnd in range(4):
        r=minimize(cbd,x,method='L-BFGS-B',options={'maxiter':400,'eps':1e-7})
        x=r.x/np.linalg.norm(r.x)
        r=minimize(cbd,x,method='Nelder-Mead',options={'maxiter':4000,'xatol':1e-9,'fatol':1e-12,'adaptive':True})
        x=r.x/np.linalg.norm(r.x)
        if cbd(x)>best-1e-8: best=min(best,cbd(x)); break
        best=cbd(x)
    dg=diagnostics(x.reshape(6,6),full=False)
    return dict(seed=seed,cBD=cbd(x),diag=dg,A=x.reshape(6,6).tolist())

if __name__=='__main__':
    N=int(sys.argv[1]); out=[]
    with Pool(4) as p:
        for res in p.imap_unordered(job,range(N)):
            out.append(res); d=res['diag']
            print(f"{res['seed']:4d} cBD={res['cBD']:.6f} c8={d['c8']:.4f} lean8={d['lean8']:.3f} regime={d['regime']:.2f} Jfrac={d['Jfrac']:.3f} k2/k1={d['gap_k2_over_k1']:.4f} fr={np.round(d['freqs'],3)}",flush=True)
            json.dump(out,open(f'{D}/adv_bd.json','w'))
    print('MIN cBD',min(o['cBD'] for o in out))
