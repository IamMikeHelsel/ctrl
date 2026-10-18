#!/usr/bin/env python3
"""Exact arithmetic only. This is not a Lean proof or a hybrid construction."""
from fractions import Fraction as F
from pathlib import Path
import json

h=F(1,2000); lower=F(18439,61000); horizon=F(53,100)
assert 604*h < lower <= 605*h
assert lower > F(1,20)
assert 1058*h+h == F(1059,2000) < horizon
assert horizon-(1058*h+h)==h
assert 2*h==F(1,1000)
B=F(3013722449,20100000000)
assert F(71,500)<B<F(3,20)

def state(t):
    return (F(1,1000)+F(39,100)*t-F(3,5)*t*t,
            F(39,100)-F(6,5)*t,-F(6,5))
def guard(z):
    x,v,a=z
    return x<=F(143,1000) and abs(v)<=F(561,50000) and -F(127,100)<=a<=-F(1,5)
hits=[k for k in range(1059) if guard(state(k*h))]
k=hits[0]; assert k==632
sigma=k*h; arrival=sigma+h
assert all(not guard(state(j*h)) for j in range(k))
assert state(sigma)[1]==F(27,2500)
assert state(arrival)[1]==F(51,5000)>0
assert arrival<F(13,40)
assert state((k-1)*h)[1]==F(57,5000)>F(561,50000)

m=state(sigma); x,v,a=m
offset=(x,x+v/4,x+v/2+a/16)
err=tuple(F(n,10**8) for n in (101533,368033,1042283))
w=(F(51,50),F(101,100),F(1))
K=max([F(9,200)]+[(offset[i]-offset[j]+err[i]+err[j])/(w[i]+w[j]) for i in range(3) for j in range(3)])
c=max(offset[i]+err[i]-w[i]*K for i in range(3))
u=-8*(x-c)-6*v-a/2
assert K==F(9,200)
assert c==F(2525673,10**8)
assert u==F(2783033,12500000)
assert -2<u<2 and u!=-F(121,100)
assert -F(121,100)+F(1,100)==-F(6,5)

# Bounds for the explicit oscillatory acceleration in the companion note.
T=F(1,20); A=-F(3,5); eps=F(1,100)
q_error=eps*T+2*eps/8
assert q_error==F(3,1000)
assert -F(61,50)<A-q_error<A+q_error<F(1,10)
assert -F(61,50)<A-eps*T<A+eps*T<F(1,10)

def pack(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,tuple): return [pack(v) for v in x]
    if isinstance(x,dict): return {k:pack(v) for k,v in x.items()}
    return x
result={
 'scope':'Exact rational checks; no Lean build, future trajectory, or C7 acceptance',
 'timing':{'lower_guard_time':lower,'min_grid_index':605,'max_index':1058,'latest_arrival':1058*h+h,'strict_reserve':h,'incoming_age':2*h,'outgoing_age':h},
 'clearance':{'prefix_ceiling':F(71,500),'C5_ceiling':B,'gap':B-F(71,500)},
 'early_first_guard':{'k':k,'sample':sigma,'arrival':arrival,'sample_state':m,'arrival_state':state(arrival),'previous_velocity':state((k-1)*h)[1],'first_zero':F(13,40),'policy_radius':K,'center':c,'first_digital_command':u,'pending_command':-F(121,100),'prefix_error':F(1,100)},
 'oscillatory_control':{'center_acceleration':A,'amplitude':eps,'loss_target_error_bound':q_error,'loss_target_lower':A-q_error,'loss_target_upper':A+q_error},
 'all_checks_pass':True}
(Path(__file__).parent/'result.json').write_text(json.dumps(pack(result),indent=2)+'\n')
print(json.dumps(pack(result),indent=2))
