"""Adversarial minimisation of span ratios with a full-rank constraint on the top skew K:
   minimise c(A) + 1e3*max(0, tau - f3/f1)^2  for c in {cBD, cT6}.
   Starts: random, the pod's SS-fail matrix, and n=6 ascent limits."""
import os; os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, json, sys
from fractions import Fraction as Fr
from multiprocessing import Pool
from scipy.optimize import minimize
from gap import frame, s_restricted, bd_basis, sub_bases, diagnostics, span_ratios
from core import rand_A
D=os.path.dirname(os.path.abspath(__file__))
T6,S3=sub_bases()
SSF=np.array([[float(Fr(x)) for x in r] for r in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'cert_ss_fail.json')))['A_num']])
ASC=[np.array(o['A']) for o in sorted(json.load(open(f'{D}/ascent_n6_0.json')),key=lambda o:-o['svK'][4])[:8]]

def obj(x,which,tau):
    A=x.reshape(6,6); A1,K1,fr,k,sv=frame(A)
    B=bd_basis() if which=='BD' else T6
    c=(s_restricted(A1,B)/k)**2
    return c+1e3*max(0,tau-fr[2]/fr[0])**2

def job(a):
    seed,which,tau=a
    rng=np.random.default_rng(4242+seed)
    st=seed%4
    if st==0: A=SSF+0.01*rng.standard_normal((6,6)); src='ssfail'
    elif st==1: A=ASC[seed%len(ASC)]+0.01*rng.standard_normal((6,6)); src='ascent'
    else: A=rand_A(6,rng,['gauss','sparse'][st-2]); src='rand'
    x=A.ravel()/np.linalg.norm(A)
    prev=9
    for it in range(8):
        r=minimize(obj,x,args=(which,tau),method='L-BFGS-B',options={'maxiter':200,'eps':1e-7}); x=r.x/np.linalg.norm(r.x)
        r=minimize(obj,x,args=(which,tau),method='Nelder-Mead',options={'maxiter':3000,'adaptive':True}); x=r.x/np.linalg.norm(r.x)
        v=obj(x,which,tau)
        if prev-v<1e-7: break
        prev=v
    A=x.reshape(6,6); cT6,cS3,cBD=span_ratios(A); dg=diagnostics(A,full=False)
    return dict(seed=seed,which=which,tau=tau,src=src,obj=obj(x,which,tau),cT6=cT6,cBD=cBD,diag=dg,A=A.tolist())

if __name__=='__main__':
    jobs=[(s,w,t) for t in [0.25,0.4] for w in ['BD','T6'] for s in range(8)]
    out=[]
    with Pool(4) as p:
        for r in p.imap_unordered(job,jobs):
            out.append(r); d=r['diag']
            print(f"{r['which']} tau={r['tau']} seed={r['seed']} src={r['src']:6s} obj={r['obj']:.6f} cT6={r['cT6']:.6f} cBD={r['cBD']:.6f} c8={d['c8']:.4f} lean8={d['lean8']:.3f} regime={d['regime']:.2f} k2/k1={d['gap_k2_over_k1']:.4f} fr={np.round(d['freqs'],3)}",flush=True)
            json.dump(out,open(f'{D}/adv_fr.json','w'))
