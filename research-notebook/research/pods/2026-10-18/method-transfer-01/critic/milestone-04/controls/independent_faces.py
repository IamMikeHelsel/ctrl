#!/usr/bin/env python3
"""Exact independent face extrema and time/physical-coordinate arithmetic."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json
w=[F(51,50),F(101,100),F(1)];K=F(9,200);v=F(3,1700);R=F(2221,40000);W=F(136350047,1250000000)
def rhs(r,e,z):return [4*(-z[0]+z[1]),4*(-z[1]+z[2]),4*((1-r/8)*z[0]+3*(r/8-1)*z[1]+(2-3*r/8)*z[2])+r*e/16]
# For fixed face the expression is affine in each remaining coordinate,
# residual and rate separately; vertices bound this finite box exactly.
faces=[]
for i in range(3):
 vals=[]
 for rate,err in product([F(8),F(12)],[-W,W]):
  for signs in product([-1,1],repeat=2):
   z=[F(0)]*3;z[i]=w[i]*K
   for k,s in zip([k for k in range(3) if k!=i],signs):z[k]=s*w[k]*K
   vals.append(rhs(rate,err,z)[i]/w[i])
 worst=max(vals);assert worst<=-v;faces.append(worst)
# For every K>=target, these exact maximizing face expressions decrease.
# Face 3's extreme choices hold over the entire rate interval [8,12].
assert 4*(w[1]-w[0])<0 and 4*(w[2]-w[1])<0
third_slopes=[F(21,40)*r-F(41,5) for r in [8,12]]
assert max(third_slopes)<0
assert faces[0]==-v
H=(R-K)/v;assert H==F(7157,1200)
physical=[w[0]*K,4*(w[0]+w[1])*K,16*(w[0]+2*w[1]+w[2])*K]
assert physical==[F(459,10000),F(1827,5000),F(1818,625)]
assert R-v*5>K
# Counter-control: a state at three weighted faces has positive, nonzero speed.
s=[-physical[0],physical[1],-physical[2]]
z=[s[0],s[0]+s[1]/4,s[0]+s[1]/2+s[2]/16]
assert z==[-w[0]*K,w[1]*K,-w[2]*K] and s[1]>0
# .04 face violation is only for the residual enclosure, not a sampled history.
kk=F(1,25);outward=rhs(F(12),W,[-w[0]*kk,w[1]*kk,kk])[2];assert outward>0
out={'passed':True,'face_normalized_upper_at_target':[str(a) for a in faces],
 'third_face_K_slope_at_rate_endpoints':[str(a) for a in third_slopes],
 'entry_time':str(H),'five_second_envelope_excess':str(R-v*5-K),
 'physical_bounds':[str(a) for a in physical],
 'late_box_nonzero_speed_state':[str(a) for a in s],
 'smaller_plateau_aggregate_outward':str(outward),
 'scope':'Exact algebra. The vertex argument covers the affine box extrema; neither counter-control constructs a sampled execution.'}
Path(__file__).with_name('independent-faces.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
