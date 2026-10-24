"""Adversarial minimisation of cHyb = max(s_BD^2, s_R1^2)/k^2 (+ penalties: f3/f1 >= tau, k2/k1 <= gmax)."""
import os; os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, json, sys
from multiprocessing import Pool
from scipy.optimize import minimize
from hybrid import chyb, chyb_fast
from adv_fr import SSF, ASC
from core import rand_A
D=os.path.dirname(os.path.abspath(__file__))
def obj(x,tau,gmax):
    h=chyb_fast(x.reshape(6,6)); fr=h[3]
    return h[0]+1e3*max(0,tau-fr[2]/fr[0])**2+1e3*max(0,h[4]-gmax)**2
def job(a):
    seed,tau,gmax=a
    rng=np.random.default_rng(31+seed)
    prev=[np.array(o['A']) for o in json.load(open(f'{D}/adv_fr.json'))]
    pool=[SSF/np.linalg.norm(SSF)]+prev+ASC[:3]
    A=pool[seed%len(pool)]+0.03*rng.standard_normal((6,6)) if seed<8 else rand_A(6,rng,'gauss')
    x=A.ravel()/np.linalg.norm(A); pv=9
    for it in range(6):
        r=minimize(obj,x,args=(tau,gmax),method='Nelder-Mead',options={'maxiter':2500,'adaptive':True}); x=r.x/np.linalg.norm(r.x)
        v=obj(x,tau,gmax)
        if pv-v<1e-6: break
        pv=v
    h=chyb(x.reshape(6,6))
    return dict(seed=seed,tau=tau,gmax=gmax,obj=obj(x,tau,gmax),cHyb=h[0],cBD=h[1],cR1=h[2],freqs=list(h[3]),gap=h[4],A=x.reshape(6,6).tolist())
if __name__=='__main__':
    jobs=[(s,t,g) for (t,g) in [(0.0,1.01),(0.25,0.98)] for s in range(10)]
    out=[]
    with Pool(4) as p:
        for r in p.imap_unordered(job,jobs):
            out.append(r)
            print(f"tau={r['tau']} gmax={r['gmax']} seed={r['seed']} obj={r['obj']:.6f} cHyb={r['cHyb']:.6f} cBD={r['cBD']:.6f} cR1={r['cR1']:.6f} gap={r['gap']:.4f} fr={np.round(r['freqs'],3)}",flush=True)
            json.dump(out,open(f'{D}/adv_hyb.json','w'))
