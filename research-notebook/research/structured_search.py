"""MF-13 search in diagonal-plus-skew coordinates; numerical evidence only.

Every real matrix is orthogonally similar to one of this form by diagonalizing
its symmetric part. Frobenius norms are invariant under orthogonal conjugation.
This mathematical reduction is not yet formalized in our Lean project.
"""
import json,time
from pathlib import Path
import numpy as np
from lyapunov_search import bases,gap_gradient,restricted

def project(a):
    return np.diag(np.diag(a))+(a-a.T)/2

def reduce(a):
    _,q=np.linalg.eigh((a+a.T)/2)
    return q.T@a@q

rng=np.random.default_rng(20261017)
bs,bk=bases(6,True),bases(6,False)
# Verify the reduction numerically before using it.
errs=[]
for _ in range(30):
    a=rng.normal(size=(6,6));r=reduce(a)
    assert np.linalg.norm(r-project(r))<1e-12
    for b in [bs,bk]:
        err=abs(np.linalg.norm(restricted(a,b),2)-np.linalg.norm(restricted(r,b),2))
        assert err<1e-11
        errs.append(err)
old=reduce(np.array(json.load(open('research/mf13-search.json'))['best_matrix']))
start=time.monotonic();best=-float('inf');best_a=None;restarts=0;steps=0;last=start
while time.monotonic()-start<120:
    restarts+=1
    if restarts%3==0:
        a=old+project(rng.normal(size=(6,6)))*10**rng.uniform(-3,0)
    else:
        a=project(rng.normal(size=(6,6)))
    a/=np.linalg.norm(a);m=np.zeros_like(a);v=m.copy()
    for it in range(1,1001):
        gap,g,_,_=gap_gradient(a,bs,bk);steps+=1
        if gap>best:best=gap;best_a=a.copy()
        if gap>1e-7:break
        g=project(g);g-=np.sum(g*a)*a
        m=.9*m+.1*g;v=.999*v+.001*g*g
        a=project(a+.015*(1-it/1200)*(m/(1-.9**it))/(np.sqrt(v/(1-.999**it))+1e-8))
        a/=np.linalg.norm(a)
        if steps%100==0:
            now=time.monotonic()
            if now-last>30:
                print(json.dumps(dict(seconds=now-start,restarts=restarts,best_gap=best)),flush=True);last=now
            if now-start>=120:break
    if best>1e-7:break
result=dict(seed=20261017,seconds=time.monotonic()-start,restarts=restarts,steps=steps,
    best_gap=best,best_matrix=best_a.tolist(),reduction_crosscheck_max_error=max(errs),
    conclusion='numerical candidate requiring exact verification' if best>1e-7 else 'No counterexample found; no universal conclusion follows.')
Path('research/mf13-structured.json').write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k!='best_matrix'}),flush=True)
