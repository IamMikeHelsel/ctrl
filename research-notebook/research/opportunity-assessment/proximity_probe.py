"""Exact-integer feasibility probes of frozen public Proximity candidates.
Does not prove the coding-theory theorem or submit any candidate.
Decimal output is illustrative; boolean and optimization decisions use integers.
"""
from math import comb
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
import json, time, subprocess, hashlib
root=Path(__file__).resolve().parent
repo=root/'proximity'
start=time.perf_counter()
p=2**31-2**24+1
n=2**18
N=2**59+1

def lower_ok(B,P,Q): return (Q-P)**12800 * 2**B <= Q**12800

def upper_ok(B,i): return (n-i)**12800 * 2**B >= n**12800

def bits(P,Q):
    with localcontext() as ctx:
        ctx.prec=65
        return str(-128*(1-Decimal(P)/Decimal(Q)).ln()/Decimal(2).ln())

def first_true(lo,hi,pred):
    while lo<hi:
        m=(lo+hi)//2
        if pred(m): hi=m
        else: lo=m+1
    return lo

P,Q=331366399,1073741824
# These are strict score-only barriers, independent of the reduction argument.
checks={
 'lower_6815_pass':lower_ok(6815,P,Q),
 'lower_6816_pass':lower_ok(6816,P,Q),
 'lower_6816_at_cell_supremum_pass':lower_ok(6816,80900,n),
 'upper_11613_pass':upper_ok(11613,122369),
 'upper_11612_pass':upper_ok(11612,122369),
 'field_capacity_split':2**128*(274980718452113030+9659282057)<=p**6,
 'orbit_original_pigeonhole':p**14*512*2**59<comb(511,272),
 'orbit_next_selected_fibres_pigeonhole':p**15*512*2**59<comb(511,273),
 'orbit_density':p**6<N*2**128,
 'orbit_alpha_avoidance':N*N*272+513<p**6,
}
# Minimum Hamming-grid numerator capable of certifying score68.16 (score only).
next_agreement_loss=first_true(80899,n//2,lambda e:lower_ok(6816,e,n))
# For each 2-power number f of fibres, b=n/f points per fibre, use the
# analogous top-coefficient/product-key parameter counts. Generalization of
# polynomial construction is NOT proved here: feasibility filter only.
rows=[]
for s in range(4,19):
 f=2**s;b=n//f
 def possible(t):
  c=max(0,t-f//2-2)
  return comb(f-1,t)>p**c*f*(N-1)
 lo=f//2;hi=f-1
 while lo<hi:
  mid=(lo+hi+1)//2
  if possible(mid):lo=mid
  else:hi=mid-1
 t=lo;c=max(0,t-f//2-2)
 passes=possible(t)
 i=n-(t*b+b-1)
 rows.append({'fibres':f,'block':b,'selected_fibres':t,'top_coefficients':c,
   'pigeonhole_pass':passes,'next_t_pigeonhole_pass':possible(t+1) if t+1<f else False,
   'degree_budget':b-1+b*(t-c-3)<=131071,
   'alpha_avoidance':N*N*t+f+1<p**6,
   'unsafe_index_if_generalized':i,'spotcheck_bits_if_generalized':bits(i,n)})
# Ordinary full-domain prescribed-top family: exact count ceiling, no Lean.
def plain(r):return comb(n,n//2+r)>p**r*2**59
lo=0;hi=10000
while lo<hi:
 m=(lo+hi+1)//2
 if plain(m):lo=m
 else:hi=m-1
r=lo
out={'revision':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
'checks':checks,'score_bits':{'lower':bits(P,Q),'lower_cell_supremum':bits(80900,n),'upper':bits(122369,n)},
'lower_6816_first_grid_numerator':next_agreement_loss,
'lower_6816_previous_grid_pass':lower_ok(6816,next_agreement_loss-1,n),
'field_capacity_unused_integer_budget':p**6//2**128-274980718452113030-9659282057,
'full_domain_prescribed_top':{'max_r_count_only':r,'count_pass':plain(r),'next_count_pass':plain(r+1),'unsafe_index_if_generalized':n//2-r,'bits_if_generalized':bits(n//2-r,n)},
'orbit_family_feasibility':rows,'elapsed_seconds':time.perf_counter()-start,
'scope':'Exact Python integer checks and unproved generalized-template feasibility filters; no Lean baseline replay or new certified coding-theory result.'}
(root/'proximity-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
