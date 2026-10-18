"""Bounded numerical exploration of MF-13, never a proof of the open conjecture.

Known example data: Kressner & Vandereycken, arXiv:2608.20875v1, Theorem 2.
Search uses their suggested symmetric/skew split and Adam; implementation here
is independent. Exact witness verification uses Python Fraction arithmetic.
"""
from __future__ import annotations
import argparse
import json
import time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np

A7 = np.array([
    [0,0,0,0,0,0,0], [0,0,0,0,0,0,0], [6,-5,-13,0,0,0,0],
    [-14,-18,0,0,0,0,0], [12,-12,11,0,0,0,0],
    [0,0,0,-6,0,-14,0], [0,0,0,6,-18,0,0]], dtype=int)
K7 = np.array([
    [0,4,-9,41,71,4,6], [-4,0,-11,-59,105,-12,3],
    [9,11,0,59,-10,36,-8], [-41,59,-59,0,9,0,2],
    [-71,-105,10,-9,0,-15,0], [-4,12,-36,0,15,0,4],
    [-6,-3,8,-2,0,-4,0]], dtype=int)

def bases(n, symmetric, normalized=True):
    out=[]
    if symmetric:
        for i in range(n):
            e=np.zeros((n,n)); e[i,i]=1; out.append(e)
    for i in range(n):
        for j in range(i+1,n):
            e=np.zeros((n,n)); e[i,j]=1; e[j,i]=1 if symmetric else -1
            out.append(e / np.sqrt(2) if normalized else e)
    return np.array(out)

def restricted(a, basis):
    images = a @ basis + basis @ a.T
    return np.einsum('kij,lij->kl', basis, images, optimize=False)

def norm_gradient(a, basis):
    b=restricted(a,basis)
    u,s,vt=np.linalg.svd(b,full_matrices=False)
    x=np.einsum('k,kij->ij', vt[0],basis)
    y=np.einsum('k,kij->ij', u[:,0],basis)
    return s[0], y@x.T + y.T@x

def gap_gradient(a, bs, bk):
    sn,sg=norm_gradient(a,bs); kn,kg=norm_gradient(a,bk)
    return kn-sn, kg-sg, sn,kn

def exact_known_check():
    b=bases(7,True,False).astype(int)
    weights=np.sum(b*b,axis=(1,2))
    images=A7@b+b@A7.T
    numer=np.einsum('kij,lij->kl', b,images)
    assert np.all(numer % weights[:,None] == 0)
    coords=numer//weights[:,None]
    m=1196*np.diag(weights)-coords.T@np.diag(weights)@coords
    size=len(m); l=[[Q(int(i==j)) for j in range(size)] for i in range(size)]; d=[]
    for j in range(size):
        dj=Q(int(m[j,j]))-sum(l[j][k]**2*d[k] for k in range(j))
        assert dj>0; d.append(dj)
        for i in range(j+1,size):
            l[i][j]=(Q(int(m[i,j]))-sum(l[i][k]*l[j][k]*d[k] for k in range(j)))/dj
    for i in range(size):
        for j in range(size):
            assert sum(l[i][k]*d[k]*l[j][k] for k in range(size)) == int(m[i,j])
    assert min(d)>=82
    assert np.array_equal(K7.T,-K7)
    nk=int(np.sum(K7*K7)); image=A7@K7+K7@A7.T; ni=int(np.sum(image*image))
    assert (nk,ni)==(53836,64387950)
    assert ni>1196*nk
    return {'symmetric_separator':1196,'ldl_pivots_positive':True,
            'minimum_pivot':str(min(d)),'skew_norm_squared':nk,
            'skew_image_norm_squared':ni,'strict_integer_margin':ni-1196*nk,
            'kind':'exact Python rational arithmetic; not Lean checked'}

def validate():
    rng=np.random.default_rng(9871)
    for n in (2,5,6,7):
        a=rng.normal(size=(n,n)); bs=bases(n,True);bk=bases(n,False)
        for basis in (bs,bk):
            assert np.allclose(np.einsum('kij,lij->kl',basis,basis),np.eye(len(basis)))
        sn=np.linalg.norm(restricted(a,bs),2);kn=np.linalg.norm(restricted(a,bk),2)
        full=np.linalg.norm(np.kron(np.eye(n),a)+np.kron(a,np.eye(n)),2)
        assert abs(max(sn,kn)-full)<1e-10
        gap,grad,_,_=gap_gradient(a,bs,bk)
        direction=rng.normal(size=(n,n));eps=1e-6
        diff=(gap_gradient(a+eps*direction,bs,bk)[0]-gap_gradient(a-eps*direction,bs,bk)[0])/(2*eps)
        assert abs(diff-np.sum(grad*direction))<1e-7
    s7=np.linalg.norm(restricted(A7,bases(7,True)),2)**2
    k7=np.linalg.norm(restricted(A7,bases(7,False)),2)**2
    assert s7<1196<k7
    return {'gradient_finite_difference_checks':'passed at n=2,5,6,7',
            'full_kronecker_crosscheck':'passed at n=2,5,6,7',
            'known_n7_symmetric_squared':s7,'known_n7_skew_squared':k7}

def search(seconds,seed,out):
    rng=np.random.default_rng(seed);bs=bases(6,True);bk=bases(6,False)
    start=time.monotonic();last=start;starts=0;steps=0;best=-float('inf');best_a=None
    history=[]
    while time.monotonic()-start<seconds:
        starts+=1
        if starts<=7:
            a=np.delete(np.delete(A7,starts-1,0),starts-1,1).astype(float)
            a+=rng.normal(scale=0.01,size=a.shape)
        elif starts%3==0 and best_a is not None:
            a=best_a+rng.normal(scale=10**rng.uniform(-3,-0.3),size=(6,6))
        else: a=rng.normal(size=(6,6))
        a/=np.linalg.norm(a);m=np.zeros_like(a);vv=m.copy()
        for it in range(1,1601):
            gap,grad,sn,kn=gap_gradient(a,bs,bk);steps+=1
            if gap>best:
                best=gap;best_a=a.copy()
                history.append({'step':steps,'gap':gap,'ratio':kn/sn,'elapsed':time.monotonic()-start})
            if gap>1e-7:
                print('NUMERICAL CANDIDATE: requires exact certificate',gap,flush=True)
                break
            grad-=np.sum(a*grad)*a
            m=.9*m+.1*grad;vv=.999*vv+.001*grad*grad
            rate=(.02 if it<=800 else .006)*(1-.85*((it-1)%800/800)**2)
            a+=rate*(m/(1-.9**it))/(np.sqrt(vv/(1-.999**it))+1e-8)
            a/=np.linalg.norm(a)
            if steps%100==0:
                now=time.monotonic()
                if now-last>=30:
                    print(json.dumps({'elapsed_s':round(now-start),'starts':starts,'steps':steps,'best_gap':best}),flush=True);last=now
                if now-start>=seconds:break
        if best>1e-7:break
    result={'seed':seed,'dimension':6,'seconds':time.monotonic()-start,'starts':starts,
            'steps':steps,'best_gap':best,'best_matrix':best_a.tolist(),
            'history':history,'candidate_threshold':1e-7,
            'conclusion':'candidate; exact verification required' if best>1e-7 else
            'No counterexample found. This is not evidence of a universal proof.'}
    out.write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k not in ('best_matrix','history')}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=0)
    p.add_argument('--seed',type=int,default=20261016);p.add_argument('--out',type=Path,default=Path('mf13-search.json'))
    args=p.parse_args(); checks={'exact_known':exact_known_check(),'numerical_validation':validate()}
    args.out.with_suffix('.checks.json').write_text(json.dumps(checks,indent=2));print(json.dumps(checks),flush=True)
    if args.seconds:search(args.seconds,args.seed,args.out)
