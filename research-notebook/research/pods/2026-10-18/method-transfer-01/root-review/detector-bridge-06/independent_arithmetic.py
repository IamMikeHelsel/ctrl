#!/usr/bin/env python3
"""Reviewer calculations; imports no builder code. These are not ODE proofs."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

out = {}
tau_lo, tau_hi = Q(39,122), Q(529,1000)
a_lo, a_hi = -Q(61,50), -Q(19,70)
gap, latency = Q(1,2000), Q(1,2000)
window = Q(1,1000)
assert tau_lo > Q(1,10)
assert a_hi < -Q(1,4)
assert a_lo*window == -Q(61,50000)
corners = []
for v,a,ev,ea in product([a_lo*window,Q(0)], [a_lo,a_hi], [-Q(1,100),Q(1,100)], [-Q(1,20),Q(1,20)]):
    mv,ma=v+ev,a+ea
    assert abs(mv)<=Q(561,50000)
    assert -Q(127,100)<=ma<=-Q(1,5)
    corners.append([str(x) for x in [v,a,ev,ea,mv,ma]])
assert Q(71,500)+Q(1,1000)==Q(143,1000)
assert 2000*tau_hi==1058
arrival=Q(1058,2000)+latency
assert arrival==Q(1059,2000)<Q(53,100)
assert gap+latency==Q(1,1000)
out['sensor_corners']=corners
out['latest_arrival']=str(arrival)
out['strict_horizon_margin']=str(Q(53,100)-arrival)

# A qualifying reading can precede the physical first zero, even without noise.
# Constant acceleration -1.2, velocity .39, position .001 is within C6's family.
t=Q(8,25)
v=Q(39,100)-Q(6,5)*t
x=Q(1,1000)+Q(39,100)*t-Q(3,5)*t*t
a=-Q(6,5)
assert t==Q(640,2000)
assert x<=Q(143,1000) and 0<v<=Q(561,50000) and -Q(127,100)<=a<=-Q(1,5)
assert t<Q(13,40) and Q(39,100)-Q(6,5)*Q(13,40)==0
out['early_guard_constant_flow']={'sample_index':640,'time':str(t),'x':str(x),'v':str(v),'a':str(a),'first_zero':str(Q(13,40)), 'scope':'exact formula; Lean trajectory instantiation is separate'}

# A lower bound on any qualifying physical time follows from velocity alone.
lower=(Q(39,100)-Q(561,50000)-Q(1,100))/Q(61,50)
assert lower==Q(18439,61000)>Q(1,10)
out['any_guard_time_lower_from_sensor_and_velocity']=str(lower)
out['scope']='Independent rational endpoint checks. Not a first-zero, sensor-stream, or hybrid proof.'
out['passed']=True
p=Path(__file__).with_name('arithmetic-result.json')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='sensor_corners'},indent=2))
