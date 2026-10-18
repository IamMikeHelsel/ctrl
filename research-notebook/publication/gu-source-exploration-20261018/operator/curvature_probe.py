#!/usr/bin/env python3
"""Exact local Clifford contraction probe. Standard-library only; not a Lean proof."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import sys
if not __debug__: raise RuntimeError("Run without -O: verification assertions are required")
N=14
sign=[1]*7+[-1]*7
omega=(1<<N)-1

def mul_blade(a,b):
    swaps=sum((b&((1<<j)-1)).bit_count() for j in range(N) if a>>j&1)
    negatives=(a&b&(((1<<N)-1)^((1<<7)-1))).bit_count()
    return (-1)**(swaps+negatives),a^b

def add(out,mask,c):
    out[mask]=out.get(mask,F(0))+c
    if not out[mask]: del out[mask]

def multiply(a,b):
    out={}
    for x,c in a.items():
        for y,d in b.items():
            s,m=mul_blade(x,y); add(out,m,s*c*d)
    return out

def bracket(a,b,mode):
    out=multiply(a,b)
    for m,c in multiply(b,a).items(): add(out,m,mode*c)
    return out

def tensor(pair_values):
    out={}
    for (a,b,c,d),v in pair_values.items():
        for i,j,s in [(a,b,1),(b,a,-1)]:
            for k,l,t in [(c,d,1),(d,c,-1)]:
                out[i,j,k,l]=F(s*t*v)
                out[k,l,i,j]=F(s*t*v)
    return out

def evaluate(name,R,expect_bianchi):
    def r(i,j,k,l): return R.get((i,j,k,l),F(0))
    for i,j,k,l in product(range(N),repeat=4):
        assert r(i,j,k,l)==-r(j,i,k,l)==-r(i,j,l,k)==r(k,l,i,j)
    bianchi=sum(r(i,j,k,l)+r(i,k,l,j)+r(i,l,j,k)!=0 for i,j,k,l in product(range(N),repeat=4))
    assert (bianchi==0)==expect_bianchi
    ricci={(i,l):sum(sign[j]*r(j,i,j,l) for j in range(N)) for i,l in product(range(N),repeat=2)}
    # Phi2 double contraction, before its required Jordan factor i.
    scalar=sum(sign[i]*ricci[i,i] for i in range(N))
    scalar_products={}
    scalar_products_raw={}
    for mode,label in [(-1,'commutator'),(1,'anticommutator')]:
        out={}
        for i,j in combinations(range(N),2):
            B={(1<<i)|(1<<j):F(1)}
            curvature={(1<<k)|(1<<l):sign[k]*sign[l]*r(i,j,k,l) for k,l in combinations(range(N),2) if r(i,j,k,l)}
            for m,c in bracket(B,curvature,mode).items(): add(out,m,sign[i]*sign[j]*c)
        if mode==-1: assert not out  # pair symmetry is sufficient
        if mode==1 and expect_bianchi: assert out==({0:-scalar} if scalar else {})
        scalar_products_raw[label]=out
        scalar_products[label]={str(k):str(v) for k,v in out.items()}
    outputs={}
    raw_outputs={}
    for twist in [False,True]:
        for mode,label in [(-1,'commutator'),(1,'anticommutator')]:
            rows=[]
            for i in range(N):
                out={}
                for j in range(N):
                    v={1<<j:F(1)}
                    if twist: v=multiply({omega:F(1)},v)
                    curvature={(1<<k)|(1<<l):sign[k]*sign[l]*r(j,i,k,l) for k,l in combinations(range(N),2) if r(j,i,k,l)}
                    for m,c in bracket(v,curvature,mode).items(): add(out,m,sign[j]*c)
                if mode==-1:
                    target={1<<l:2*sign[l]*ricci[i,l] for l in range(N) if ricci[i,l]}
                    if twist: target=multiply({omega:F(1)},target)
                    assert out==target
                if mode==1 and expect_bianchi: assert not out
                rows.append(out)
            raw_outputs[('omega_' if twist else '')+label]=rows
            outputs[('omega_' if twist else '')+label]={'nonzero_rows':sum(bool(x) for x in rows),'all_rows':[{str(k):str(v) for k,v in row.items()} for row in rows]}
    if expect_bianchi:
        # Q=-i scalar. A second J contributes i*(-i)*{e_i,scalar}=2 scalar e_i.
        for i in range(N):
            einstein=raw_outputs['commutator'][i].copy()
            # Evaluate both Jordan products via i*i=-1, using the computed inner product.
            for mask,coefficient in bracket({1<<i:F(1)},scalar_products_raw['anticommutator'],1).items():
                add(einstein,mask,F(1,2)*coefficient)
            target={}
            for l in range(N):
                g=sign[i] if i==l else 0
                add(target,1<<l,2*sign[l]*(ricci[i,l]-F(1,2)*scalar*g))
            assert einstein==target
    return {'name':name,'bianchi_violations':bianchi,'ricci_nonzero_entries':sum(bool(v) for v in ricci.values()),'scalar_curvature':str(scalar),'Phi2_contractions_before_i':scalar_products,'outputs':outputs}

cases=[]
# Full split-signature constant sectional curvature +1.
cases.append(evaluate('constant_sectional_curvature',tensor({(i,j,i,j):sign[i]*sign[j] for i,j in combinations(range(N),2)}),True))
# Nonzero Weyl tensor supported in positive 4-plane; all diagonal Ricci sums cancel.
cases.append(evaluate('nonzero_Ricci_flat_Weyl',tensor({(0,1,0,1):1,(0,2,0,2):-1,(1,3,1,3):-1,(2,3,2,3):1}),True))
# Pair symmetry and pair antisymmetry alone do not imply algebraic Bianchi.
cases.append(evaluate('Bianchi_violating_control',tensor({(0,1,2,3):1}),False))
# Single nonzero mixed-sign sectional component tests both raising conventions.
cases.append(evaluate('mixed_signature_sectional',tensor({(0,7,0,7):-1}),True))
# Kulkarni-Nomizu h wedge g with off-diagonal h across positive/negative directions.
def g(i,j): return sign[i] if i==j else 0
def h(i,j): return F(1) if (i,j) in [(0,7),(7,0)] else F(0)
Rkn={(i,j,k,l):h(i,k)*g(j,l)+h(j,l)*g(i,k)-h(i,l)*g(j,k)-h(j,k)*g(i,l) for i,j,k,l in product(range(N),repeat=4)}
Rkn={k:v for k,v in Rkn.items() if v}
cases.append(evaluate('off_diagonal_Kulkarni_Nomizu',Rkn,True))
assert cases[-1]['ricci_nonzero_entries']==2
assert cases[0]['outputs']['commutator']['nonzero_rows']==14
assert cases[1]['ricci_nonzero_entries']==0
assert cases[2]['outputs']['anticommutator']['nonzero_rows']>0
out={'status':'pass','signature':[7,7],'method':'exact Fraction coefficients, sparse signed Clifford blades','boundary':'finite executable evidence plus separately written hand derivation; no Lean certification or claim to author-selected operator','cases':cases}
Path(__file__).with_name('curvature-probe-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({x['name']:{'bianchi_violations':x['bianchi_violations'],'ricci_nonzero_entries':x['ricci_nonzero_entries'],'commutator_rows':x['outputs']['commutator']['nonzero_rows'],'anticommutator_rows':x['outputs']['anticommutator']['nonzero_rows']} for x in cases},indent=2))
