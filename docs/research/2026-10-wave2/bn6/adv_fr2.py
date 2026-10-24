"""Like adv_fr but also forces a spectral gap on the top skew singular value (k2/k1 <= gmax),
to rule out that cBD<1 is an artefact of near-degenerate top skew singular vectors."""
import os; os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, json, sys
from multiprocessing import Pool
from scipy.optimize import minimize
from gap import frame, s_restricted, bd_basis, diagnostics, span_ratios
from adv_fr import SSF
from core import rand_A
D=os.path.dirname(os.path.abspath(__file__))
def obj(x,tau,gmax):
    A=x.reshape(6,6); A1,K1,fr,k,sv=frame(A)
    c=(s_restricted(A1,bd_basis())/k)**2
    return c+1e3*max(0,tau-fr[2]/fr[0])**2+1e3*max(0,sv[1]/sv[0]-gmax)**2
def job(a):
    seed,tau,gmax=a
    rng=np.random.default_rng(99+seed)
    prev=json.load(open(f'{D}/adv_fr.json'))
    bases_=[SSF/np.linalg.norm(SSF)]+[np.array(o['A']) for o in prev if o['which']=='BD']
    A=bases_[seed%len(bases_)]+0.02*rng.standard_normal((6,6)) if seed<6 else rand_A(6,rng,'gauss')
    x=A.ravel()/np.linalg.norm(A); pv=9
    for it in range(8):
        r=minimize(obj,x,args=(tau,gmax),method='Nelder-Mead',options={'maxiter':4000,'adaptive':True}); x=r.x/np.linalg.norm(r.x)
        r=minimize(obj,x,args=(tau,gmax),method='L-BFGS-B',options={'maxiter':200,'eps':1e-7}); x=r.x/np.linalg.norm(r.x)
        v=obj(x,tau,gmax)
        if pv-v<1e-7: break
        pv=v
    A=x.reshape(6,6); cT6,cS3,cBD=span_ratios(A); d=diagnostics(A,full=False)
    return dict(seed=seed,tau=tau,gmax=gmax,obj=obj(x,tau,gmax),cBD=cBD,cT6=cT6,diag=d,A=A.tolist())
if __name__=='__main__':
    jobs=[(s,0.3,g) for g in [0.97,0.9] for s in range(8)]
    out=[]
    with Pool(4) as p:
        for r in p.imap_unordered(job,jobs):
            out.append(r); d=r['diag']
            print(f"gmax={r['gmax']} seed={r['seed']} obj={r['obj']:.6f} cBD={r['cBD']:.6f} cT6={r['cT6']:.6f} c8={d['c8']:.4f} lean8={d['lean8']:.3f} regime={d['regime']:.2f} k2/k1={d['gap_k2_over_k1']:.4f} fr={np.round(d['freqs'],3)}",flush=True)
            json.dump(out,open(f'{D}/adv_fr2.json','w'))
