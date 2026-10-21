"""Independent exact preflight arithmetic. Not an execution or Lean proof."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
checks={}
def save(name,**items):
    checks[name]={k: {'exact':str(v),'decimal':float(v)} if isinstance(v,Q) else v for k,v in items.items()}
a,d=Q(3,2000),Q(1,2000)
M=Q(103,1000)
oldR,R=Q(2221,40000),Q(567,10000)
Kmax=Q(1,16)
def W0(K): return M+a*(384*K+Q(618,1000))
def S(K): return 96*K+6*W0(K)
def W1(K): return M+8*d+S(K)*(a-d)
assert W1(oldR)>2*oldR
assert W1(R)<2*R
assert S(Kmax)<8 and S(R)>0
assert 2-Q('0.099456')>0
save('outer_cube',certificate_radius_threshold=Q('0.107623562')/(2-Q('0.099456')),old_radius=oldR,old_split=W1(oldR),old_failed_margin=2*oldR-W1(oldR),new_radius=R,new_split=W1(R),new_margin=2*R-W1(R),slope_at_max=S(Kmax),all_K_margin_slope=2-Q('0.099456'))
W=M+8*d+108*R*(a-d)
Wr=Q(1132,10000)
assert W<=Wr
assert 24*R+Q(93,1000)<2
assert 24*Kmax+Q(93,1000)<2
save('closed_cube',digital_slope=108*R,residual=W,rounded_residual=Wr,residual_round_margin=Wr-W,clip_margin=2-(24*R+Q(93,1000)),inflated_clip_margin=2-(24*Kmax+Q(93,1000)))
K=Q(9,200);delta=Q(3,5000)
w0,w1=Q(51,50),Q(101,100)
def third_face(K,W,r=Q(12)):
    z0,z1,z2=-w0*K,w1*K,K
    return 4*((1-r/8)*z0+3*(r/8-1)*z1+(2-3*r/8)*z2)+r*W/16
assert third_face(K,Wr)==-delta
assert third_face(K,Q(115,1000))>0
assert third_face(K,Wr)>-Q(3,1700)
assert Q(4,100)*K/w0>delta and Q(4,100)*K/w1>delta
save('weighted_faces',third_repaired=third_face(K,Wr),third_naive=third_face(K,Q(115,1000)),old_drift=Q(3,1700),new_drift=delta,first_normalized_inward=Q(4,100)*K/w0,second_normalized_inward=Q(4,100)*K/w1,plateau_residual_ceiling=Q(19,10)*K/Q(3,4))
# Algebraic failure if S<=8 is omitted: actual overlap=0, full age=a.
Sbad=Q(9); actual=Sbad*a; false_bound=8*d+Sbad*(a-d)
assert actual>false_bound
save('overlap_missing_sign_counterexample',digital_slope=Sbad,actual_pending_overlap=Q(0),actual_increment=actual,claimed_increment=false_bound,gap=actual-false_bound)
# The bound follows by exact identity for h<=a, ell<=d, 0<=S<=8:
# [8d+S(a-d)]-[8ell+S(h-ell)] = S(a-h)+(8-S)(d-ell).
# This records symbolic coefficients; positivity is conditional on those premises.
assert (8*d+S(R)*(a-d))-(8*Q(0)+S(R)*a)==(8-S(R))*d
save('overlap_identity',premises=['0<=S<=8','0<=ell<=h<=a','ell<=d<=a'],identity='budget-actual = S*(a-h)+(8-S)*(d-ell)',exact_check=True)
# Distinct command sides at dispatch (n+1): right uses n+1; incoming left uses n.
T=Q(1,1000);n=Q(7);sample=n*T;next_dispatch=(n+1)*T+d
assert next_dispatch-sample==a
assert next_dispatch-(n+1)*T==d
save('clock',period=T,delay=d,old_reading_age_at_left_dispatch=next_dispatch-sample,new_reading_age_at_right_dispatch=next_dispatch-(n+1)*T,postzero_upper_bound=Q(529,1000)+T+d,old_braking_horizon=Q(530,1000),scope='bound gap, not a constructed reachable latest stop')
# Same policy box and forward certificate, if the new moving-box proof is completed.
Kpolicy=Q(2407079,50250000)
forward=Q(3013722449,20100000000)
assert w0*Kpolicy<R
assert forward<Q(15,100)
save('policy_conditional',policy_Kmax=Kpolicy,weighted_to_outer_margin=R-w0*Kpolicy,forward_ceiling=forward,clearance_margin=Q(15,100)-forward,new_entry_duration_bound=(Kpolicy-K)/delta,old_entry_duration_bound=(Kpolicy-K)/Q(3,1700),scope='same policy arithmetic; requires new weighted execution proof')
noise=(Q(1,100)-Q(-1,100))/T
assert noise==20 and noise/Q(1,20)==400
root=json.loads(subprocess.check_output([sys.executable,str(HERE/'inputs/measurement_counterexample.py')],text=True))
recorded=json.loads((HERE/'inputs/measurement_counterexample.json').read_text())
assert root==recorded and Q(root['derived_acceleration_m_per_s2'])==noise
save('measurement',noise=noise,allowance_multiple=noise/Q(1,20),root_replay_matches=True,scope='attaining scalar sensor-box example, not observed Franka noise')
# Independent stationary balance: Kp=8, Kv=6, Ka=.5.
ex,ev,ea,target=-Q(1,1000),-Q(1,100),-Q(1,20),Q(1,100)
offset=(-8*ex-6*ev-ea/2+target)/8
assert offset==Q(103,8000)
u=-8*(offset+ex)-6*ev-ea/2
assert u==-target and abs(u)<2
assert ea>Q(-1,5)  # fails the acceleration part of C5's admission guard
bias=json.loads(subprocess.check_output([sys.executable,str(HERE/'inputs/holding_bias_witness.py')],text=True))
assert bias==json.loads((HERE/'inputs/holding_bias_witness.json').read_text())
assert Q(bias['equilibrium_offset_m'])==offset
save('holding_bias',offset=offset,command=u,equilibrium_balance=u+target,not_C5_guard=True,root_replay_matches=True,scope='law-level equilibrium only; no admission reachability or universal controller lower bound')
for row in json.loads((HERE/'INPUTS.json').read_text()):
    assert hashlib.sha256((HERE/row['copy']).read_bytes()).hexdigest()==row['sha256'],row['copy']
result={'scope':'Independent rational preflight; no trajectory proof, no new Lean acceptance','checks':checks,'input_hashes_preserved':True}
(HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
