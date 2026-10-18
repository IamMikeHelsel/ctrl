"""Finite exact-arithmetic checks; these are Python checks, not Lean proofs."""
import json
from pathlib import Path
from exterior_core import *

checks=0

def check(condition):
    global checks
    if not condition:
        raise AssertionError(f'Failed check #{checks+1}')
    checks += 1

B=basis()
check(len(B)==256)
check(blade(2,1)=={(1,2):Fraction(-1)})
check(blade(1,1)=={})
for f in B:
    k=len(next(iter(f)))
    check(hodge(hodge(f))==scale((-1)**(k*(8-k)),f))
    check(wedge(f,hodge(f))==blade(*range(1,9)))
    for sig in [(1,)*7+(-1,), (1,)*4+(-1,)*4]:
        check(hodge(hodge(f,sig),sig)==scale((-1)**(k*(8-k)+sig.count(-1)),f))
    for i in range(1,9):
        check(source_interior(blade(i),f)==contract_vector(i,f))
        for j in range(1,9):
            check(add(symbol(i,symbol(j,f)),symbol(j,symbol(i,f)))==scale(2 if i==j else 0,f))
    if k==4:
        p,m=cleave(f),cleave(f,-1)
        check(add(p,m)==f)
        check(cleave(p)==p and cleave(m,-1)==m)
        check(cleave(p,-1)=={} and cleave(m)=={})
        check(hodge(p)==p and hodge(m)==scale(-1,m))
for f in B:
    for g in B:
        k=len(next(iter(f)));l=len(next(iter(g)))
        check(wedge(f,g)==scale((-1)**(k*l),wedge(g,f)))
# Source mid-degree + basis has 35 independent vectors. Complement-pair pivots
# make independence exact: select 4-subsets missing 8, each pivot distinct.
pos=[cleave(blade(*a)) for a in combinations(range(1,8),4)]
check(len(pos)==35)
for a,p in zip(combinations(range(1,8),4),pos):
    check(p[a]==Fraction(1,2))
    check(sum(1 for q in pos if a in q)==1)
# Explicitly detect wrong-sign star and missing 1/2 projector normalization.
f=blade(1,2,3,4)
check(add(f,hodge(f)) != cleave(f))
check(scale(-1,hodge(hodge(blade(1)))) != scale(-1,blade(1)))
result={'status':'PASS','exact_assertions':checks,'basis_size':256,
 'scope':'Reconstructed exterior operations and unprojected symbol only; final thesis symbol matrix and six determinants NOT reproduced',
 'source':'1992 thesis Appendix A.1 printed p61/PDF67; Euclidean dimension8',
 'lean_proofs':False,'external_code_executed':False}
Path(__file__).with_name('core-check-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
