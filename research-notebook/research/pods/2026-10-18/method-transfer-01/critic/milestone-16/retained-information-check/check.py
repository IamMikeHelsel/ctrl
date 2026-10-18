#!/usr/bin/env python3
from fractions import Fraction as F
from pathlib import Path
import json
P=Path(__file__).resolve().parent
w=[F(51,50),F(101,100),F(1)]; E=list(map(lambda n:F(n,100000000),[101533,368033,1042283]));target=F(9,200)
def policy(x,v,a):
 A=[x,x+v/4,x+v/2+a/16]
 pairs={(i,j):(A[i]-A[j]+E[i]+E[j])/(w[i]+w[j]) for i in range(3) for j in range(3)}
 K=max(target,*pairs.values());lower=[A[i]+E[i]-w[i]*K for i in range(3)];c=max(lower)
 return K,c,c+w[0]*K,pairs,lower
x=F(143,1000);v=F(561,50000);a=F(-127,100);ahi=F(-27,28)
K,c,U,pairs,lower=policy(x,v,a)
assert K==F(2266829,50250000) and c==F(2088856217,20100000000) and U==F(3013722449,20100000000)
assert F(-127,100)<=a<=ahi<=F(-1,5)
assert [ij for ij,val in pairs.items() if val==K]==[(1,2)]
assert [i for i,z in enumerate(lower) if z==c]==[1]
root=json.loads((P/'inputs/root-idea.json').read_text());n=0
for box in ['original','proposed_upper_acceleration']:
 for item in root[box]['corners']:
  r,cc,u,_,_=policy(x,F(item['velocity']),F(item['acceleration']))
  assert (r,cc,u)==tuple(F(item[k]) for k in ['radius','center','ceiling']);n+=1
# Conditional envelope algebra only; no physical theorem is accepted here.
t=F(18439,61000); assert t>F(3,10) and 8*(t-F(1,20))>2
assert F(-6,5)+F(13,10)*F(1,7)==F(-71,70)
assert F(-71,70)+F(1,20)==F(-27,28)
# exp(2) exceeds the sum through degree four, which is exactly seven.
from math import factorial
assert sum(F(2**k,factorial(k)) for k in range(5))==7
result={'passed':True,'scope':'Exact fixed-policy arithmetic and conditional rational envelope algebra; no Lean build, reachability or new physical acceleration theorem','measurement':list(map(str,[x,v,a])),'radius':str(K),'center':str(c),'ceiling':str(U),'clearance_margin':str(F(3,20)-U),'active_radius_pair':[1,2],'active_center_coordinate':1,'narrowed_box_membership':True,'narrow_upper_acceleration':str(ahi),'narrow_box_subset_of_old_guard':True,'matching_global_upper_source':'ClearancePolicy.forward_upper','old_corner_equality_source':'ClearancePolicy.exact_corners','root_corner_rows_recomputed':n,'earliest_guard_time_conditional':str(t),'conditional_exponent_lower':str(8*(t-F(1,20))),'conditional_physical_upper':str(F(-71,70)),'conditional_sensor_upper':str(ahi),'physical_corner_reachability_established':False}
(P/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
