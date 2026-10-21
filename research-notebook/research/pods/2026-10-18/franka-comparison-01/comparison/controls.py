#!/usr/bin/env python3
"""Semantic controls, with explicit success and rejection predicates."""
import argparse,json
from pathlib import Path
from fractions import Fraction
import numpy as np
from compare import Governor,transition,segment,S,K,EQ,policy_c5
from terminal_interval import check as exact_tail

p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
cfg=json.loads(Path(__file__).with_name('inputs.json').read_text());g=Governor(cfg)
r=cfg['rate_per_second'];T=cfg['sample_period_seconds'];D=cfg['dispatch_delay_seconds']
checks={};evidence={}
# Independent analytic two-flow state vs augmented matrix, rational test data.
errors=[]
for n in range(1,21):
 s=np.array([.1+n/10000,(n-10)/2000,-n/25]);old=(n-11)/10;c=.11+n/10000;eta=(n-10)*.009
 d0=(1 if n%2 else -1)*.01;d1=(1 if n%3 else -1)*.01;u=8*c-K@s+eta
 q0=np.r_[s,old];pred=g.F@q0+g.B*c+g.G@np.array([eta,d0,d1])
 s1,*_=segment(s,old,d0,r,D);s2,*_=segment(s1,u,d1,r,T-D)
 errors.append(float(np.max(abs(pred-np.r_[s2,u]))))
checks['two_subinterval_map_matches_independent_analytic_flow']=max(errors)<1e-13;evidence['map_max_error']=max(errors)
# Confirm first command is calculated from measured state, not from hidden truth.
m=np.array(cfg['initial_cases'][0]['measurement']);old=-1.21;feasible,_=g.interval(m,old);c=min(.14,feasible[1]);u=8*c-K@m
firstmax=0.
from itertools import product
for signs in product([-1,1],repeat=3):
 eps=np.array(signs)*g.sensor;s=m+eps
 for d0,d1 in product([-.01,.01],repeat=2):
  s1,*_=segment(s,old,d0,r,D);s2,*_=segment(s1,u,d1,r,T-D)
  pred=g.F@np.r_[m,old]+g.B*c+g.H@eps+g.G0@np.array([d0,d1])
  firstmax=max(firstmax,float(np.max(abs(pred-np.r_[s2,u]))))
checks['first_known_command_state_box_map_matches']=firstmax<1e-13;evidence['first_box_max_error']=firstmax
# Deliberate wrong topology: apply new command immediately rather than retaining old.
s=m;unew=8*c-K@m
right=np.r_[g.AT@s+(g.AR@g.BD)*old+g.BR*unew,unew]
wrong=np.r_[g.AT@s+g.BT*unew,unew]
checks['zero_delay_replacement_rejected']=np.max(abs(right-wrong))>1e-3;evidence['wrong_delay_state_error']=float(np.max(abs(right-wrong)))
# Pending memory is not determined by the three physical coordinates.
q=np.array([c,0,0,2.]);z=S@(q-EQ*c)
checks['missing_fourth_coordinate_rejected']=abs(z[3])>.014 and np.max(abs(z[:3]))==0;evidence['pending_memory_z']=z.tolist()
# The linear model must not silently continue beyond the saturation threshold.
raw=3.;lin=g.AT@s+g.BR*raw;clipped=g.AT@s+g.BR*2.
checks['unclipped_linear_model_outside_domain_rejected']=np.max(abs(lin-clipped))>1e-3
# Arbitrary within-half disturbance is not a single scalar average times Gamma.
h=D/2;z0=np.zeros(3);z1,*_=segment(z0,0,.01,r,h);z2,*_=segment(z1,0,-.01,r,h)
_,bh=transition(r,D);averages=z2/bh
checks['arbitrary_disturbance_scalar_reduction_rejected']=float(np.ptp(averages))>1e-3;evidence['component_effective_averages']=averages.tolist()
# Deliberate rate-switch case is outside the fixed-r model, with measured mismatch.
z0=np.array([.14,-.01,-1.17]);z1,*_=segment(z0,-1.21,0,8,D/2);z2,*_=segment(z1,-1.21,0,12,D/2)
constant,*_=segment(z0,-1.21,0,8,D)
checks['time_varying_rate_excluded_and_distinguished']=np.max(abs(z2-constant))>1e-5;evidence['rate_switch_map_error']=float(np.max(abs(z2-constant)))
# Endpoints alone can miss a real interior position maximum in this physical model.
z0=np.array([.1499999,.001,-2.]);end,mn,mx=segment(z0,-2,0,8,T)
checks['endpoint_only_safety_rejected']=z0[0]<.15 and end[0]<.15 and mx>.15;evidence['endpoint_only_witness']={'initial':z0.tolist(),'final':end.tolist(),'peak':mx}
checks['age_reset_rejected']=T+D>.001;evidence['actual_maximum_age_seconds']=T+D
# A tiny terminal box fails with persistent errors, even though nominal F is Schur.
bad=exact_tail(Fraction(1,1000))
checks['persistent_noise_small_box_rejected']=not bad['checks']['all_exact_interval_endpoints_inside_terminal_box'];evidence['small_box_result']=bad
checks['nominal_policy_matches_frozen_C5']=abs(policy_c5(m)[0]-.09573033)<1e-14 and policy_c5(m)[1]==.045
checks['nonempty_full_robust_first_plan']=feasible is not None and feasible[0]<=feasible[1];evidence['nominal_initial_reference_interval']=feasible
# Exact steady state: eta+d drives offset (eta+d)/8 even at unchanged c.
bias=(Fraction(93,1000)+Fraction(1,100))/8
checks['perfect_tracking_with_bounded_bias_rejected']=bias==Fraction(103,8000) and bias>Fraction(1,100)
evidence['allowed_static_position_bias_m']=str(bias)
# Genuine state-dependent constraint, kept outside the scored C5-admission cases.
active_m=np.array([.13,.08,-.2]);interval,reason=g.interval(active_m,-1.21)
wrong_slacks=g.bounds-g.rows@np.r_[active_m,-1.21]-g.coeff*.135
checks['state_dependent_plan_is_not_a_generic_clamp']=interval is not None and interval[1]<.135 and wrong_slacks.min()<0
evidence['outside_guard_active_constraint']={'measurement':active_m.tolist(),'feasible_interval':interval,'generic_clamp_min_slack':float(wrong_slacks.min()),'binding_kind':g.kinds[int(np.argmin(wrong_slacks))],'not_a_scored_comparison_case':True}
checks={k:bool(v) for k,v in checks.items()}
result={'checks':checks,'evidence':evidence,'passed':all(checks.values()),'scope':'Control rejection predicates are mathematical/model distinctions. Floating tests are not Lean or validated trajectory proofs.'}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(checks,indent=2));assert result['passed']
