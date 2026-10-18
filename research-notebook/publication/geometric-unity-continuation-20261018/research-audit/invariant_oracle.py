#!/usr/bin/env python3
"""Exact signed-blade checks. Supplemental finite evidence; not a Lean proof."""
import json
from pathlib import Path
N=14
OMEGA=(1<<N)-1
# e_i^2 = +1 for i<7, -1 otherwise. An element is (real,imag,mask).
def mul(x,y):
    a,b,p=x; c,d,q=y
    swaps=sum((q & ((1<<i)-1)).bit_count() for i in range(N) if (p>>i)&1)
    negatives=(p&q&(((1<<N)-1)^((1<<7)-1))).bit_count()
    s=(-1)**(swaps+negatives)
    return (s*(a*c-b*d),s*(a*d+b*c),p^q)
def star(x):
    a,b,p=x; r=p.bit_count(); s=(-1)**(r*(r+1)//2)
    return s*a,-s*b,p
def neg(x): return -x[0],-x[1],x[2]
def eq(x,y): return x==y or x[:2]==y[:2]==(0,0)
def sub(x,y):
    if x[2]==y[2]: return x[0]-y[0],x[1]-y[1],x[2]
    raise ValueError('this checker only subtracts matching blades')
def comm(x,y): return sub(mul(x,y),mul(y,x))
one=(1,0,0); om=(1,0,OMEGA); imag=(0,1,0)
vs=[(1,0,1<<i) for i in range(N)]
bs=[mul(vs[i],vs[j]) for i in range(N) for j in range(i+1,N)]
assert mul(om,om)==one and star(om)==neg(om)
for v in vs: assert mul(om,v)==neg(mul(v,om))
for b in bs: assert mul(om,b)==mul(b,om)
counts={}
for label,domain,twister in [('Phi1',vs,om),('Phi2',bs,mul(imag,om))]:
    for x in domain:
        assert star(x)==neg(x)
        tx=mul(twister,x)
        assert star(tx)==neg(tx)
        assert tx[2]!=x[2] # coefficient-independent basis supports
        for b in bs:
            assert eq(comm(b,tx),mul(twister,comm(b,x)))
    counts[label]={'domain_basis':len(domain),'skew_checks':2*len(domain),
                   'disjoint_support_checks':len(domain),'infinitesimal_equivariance_checks':len(bs)*len(domain)}
out={'status':'pass','method':'integer Gaussian coefficients and bitmask Clifford multiplication',
     'signature':[7,7],'volume_square':1,'volume_star_sign':-1,'checks':counts,
     'boundary':'Finite algebra checks only. Full Spin equivariance and invariant-space dimension theorem are hand proofs, not Lean-certified here.'}
Path(__file__).with_name('invariant-oracle-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
