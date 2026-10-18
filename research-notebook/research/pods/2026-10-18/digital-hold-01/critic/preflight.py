"""Independent exact preflight; no trajectory or Lean acceptance is implied."""
from fractions import Fraction as F
from itertools import product
from decimal import Decimal, localcontext
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
R = F(2221,40000)
h = F(1,1000)
M = F(93,1000)
D = F(1,100)
W = 2*R

def show(x):
    return {"exact":str(x),"decimal":float(x)}

# Independently simplify signs before maximizing: on r in [8,12],
# |4r-64|+|160-12r|+|12r-96| = 128-4r.
# Thus under a generic mismatch bound B the endpoint maxima are
# 96R+4B and 80R+6B, and at B=2R the maximum is104R.
rate_endpoints = (F(8),F(12))
slopes = [((128-4*r)*R+(r/2)*W) for r in rate_endpoints]
assert max(slopes)==104*R
slope92_witness = {"r":8,"z_over_R":[-1,1,0],"w":0,
                   "actual_abs_slope":show(96*R),
                   "rejected_bound":show(92*R)}
assert 96*R>92*R

# Cross-check the transformed identity in independently generated rational
# physical coordinates, including non-vertex interior points.
identity_checks = 0
for r,x,v,a,w in product((F(8),F(9),F(12)), (F(-1,7),F(2,9)),
                         (F(3,11),F(-2,13)), (F(-1,17),F(5,19)),
                         (F(-3,23),F(7,29))):
    z0,z1,z2=x,x+v/4,x+v/2+a/16
    k=-8*x-6*v-a/2
    lhs=-8*v-6*a-r*(k+w-a)/2
    rhs=(4*r-64)*z0+(160-12*r)*z1+(12*r-96)*z2-r*w/2
    assert lhs==rhs
    identity_checks+=1

# Proposed bounded-prefix refinement. These arithmetic checks do NOT prove
# the required prefix/one-sided derivative theorem or continuous invariance.
L0=208*R+6*(M+D)
W0=M+D+h*L0
L1=96*R+6*W0
W1=M+D+h*L1
assert W0>W and W1<W
coarse_sup=(M+D+96*h*R)/(1-6*h)
sharp_sup=max((M+D+96*h*R)/(1-4*h), (M+D+80*h*R)/(1-6*h))
assert sharp_sup<W and coarse_sup<W
screen=M+D+104*R*h
assert screen<W
assert M+D+104*R*F(2,1000)>W
assert 24*R+M+D<2

# An age upper bound alone admits an observation in the future.
t,s=F(0),F(1)
assert t-s<=h and not s<=t

# Omit the first command law and use a permissible pending target q=2.
# Initial physical state is (R,0,0), hence every transformed coordinate is R.
# With r=12 and q=2 held, a(t)=2(1-exp(-12t))>0 for t>0.
# Its integral twice implies x(t)>R immediately. Numerical evaluation is
# only an illustration; the positivity argument is exact.
with localcontext() as ctx:
    ctx.prec=70
    dt=Decimal(1)/1000
    rr=Decimal(12)
    q=Decimal(2)
    dx=q*(dt*dt/2-dt/rr+(1-(-rr*dt).exp())/(rr*rr))
    assert dx>0
    pending_dx=str(dx)

# A legitimate dispatch creates an acceleration derivative jump.
# q=0 before tau; q=M after tau; r=8; state at tau is zero.
# Left a'=0, right a'=8M=.744. State remains continuous.
jump=8*M
assert jump!=0

inputs=[
 'AGENTS.md',
 'research/pods/2026-10-18/digital-hold-01/CHARTER.txt',
 'research/controls-scope-review-20261018/ASSESSMENT.txt',
 'research/controls-scope-review-20261018/NEXT-GATE.txt',
 'research/controls-scope-review-20261018/AGE-BUDGET.txt',
 'research/controls-scope-review-20261018/COMMENTS.txt',
 'research/controls-scope-review-20261018/age_budget.py',
 'research/adjacent-controls/variable-response/sampled-handoff/RobustHold.lean',
 'research/adjacent-controls/variable-response/sampled-handoff/Capture.lean',
 'research/adjacent-controls/variable-response/sampled-handoff/Handoff.lean',
 'research/adjacent-controls/variable-response/sampled-handoff/verification.json',
 'research/adjacent-controls/variable-response/sampled-handoff/hold-scope.txt',
]
result={
 'status':'preflight only; no frozen builder statement reviewed',
 'conditional_slope':show(max(slopes)),
 'independent_identity_checks':identity_checks,
 'corrected_92R_negative_control':slope92_witness,
 'one_ms_screen':show(screen),'screen_slack':show(W-screen),
 'direct_prefix_slope_L0':show(L0),'first_refinement_W0':show(W0),
 'second_slope_L1':show(L1),'second_refinement_W1':show(W1),
 'second_refinement_slack':show(W-W1),
 'coarse_sup_bound':show(coarse_sup),'sharp_sup_bound':show(sharp_sup),
 'authority_including_d':show(24*R+M+D),
 'age_only_future_witness':{'t':'0','s':'1','age':'-1','upper_age_test':True,'causal':False},
 'missing_initial_command_witness':{'initial_state':['R','0','0'],'pending_target':'2','r':'12',
   'position_excess_at_1ms_numerical':pending_dx,
   'exact_reason':'a(t)=2(1-exp(-12t))>0 for t>0, so v(t)>0 and x(t)>R'},
 'classical_derivative_dispatch_witness':{'left_accel_derivative':'0','right_accel_derivative':str(jump),
   'continuous_state':True,'two_sided_acceleration_derivative_at_dispatch':False},
 'input_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in inputs},
 'limits':['Exact scalar arithmetic and analytic counterexamples only.',
           'Prefix safety, piecewise dynamics and general existence remain proof obligations.',
           'A failed sufficient age bound is not an unsafe trajectory.']
}
(OUT/'preflight-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
