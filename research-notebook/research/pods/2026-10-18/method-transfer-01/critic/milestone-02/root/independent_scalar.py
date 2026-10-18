"""Independent coefficient and coverage check; external graph premise is assumed."""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib

P=Path(__file__).resolve().parent
I=F(1601,40000);R=F(2491,100000);a=F(493,625);b=F(4,5)
# Coefficients are constant, linear, quadratic. Derive directly after substituting
# x=1-1/(2c) in c^2(I+completionEnvelope(x,1/2)).
mid=(F(3,8),F(-7,8),I+F(17,32))
upper=(F(-1,8),F(3,8),I-F(1,4))
mid_gap=(R-mid[0],-mid[1],R-mid[2])
upper_gap=(R-upper[0],-upper[1],R-upper[2])
value=lambda p,c:p[0]+p[1]*c+p[2]*c*c
assert F(1,2)<F(3,4)<a<b<1
assert mid_gap[2]<0
assert value(mid_gap,a)>0 and value(mid_gap,b)>0
chord_slope=(value(mid_gap,b)-value(mid_gap,a))/(b-a)
chord=(value(mid_gap,a)-chord_slope*a,chord_slope,F(0))
difference=tuple(u-v for u,v in zip(mid_gap,chord))
assert difference==(mid_gap[2]*a*b,-mid_gap[2]*(a+b),mid_gap[2])
cap_margin=R-I*a*a
assert I>0 and cap_margin>0
C,Bneg,A=upper_gap
B=-Bneg
delta=4*A*C-B*B
assert A>0 and delta>0
assert (4*A*C,-4*A*B,4*A*A)==(B*B+delta,-4*A*B,4*A*A)
# Branch selection under x=1-1/(2c): x<=3/8 iff c<=4/5 for c>0.
for c in [a,b,F(9,10)]:
    x=1-1/(2*c)
    assert (x<=F(3,8))==(c<=b)
    expected=3*x*x/2-5*x/4+F(9,32) if c<=b else x*(F(1,2)-x)/2
    assert c*c*(I+expected)==value(mid if c<=b else upper,c)
assert F(1,25)+F(1,20000)/2==I

copied=json.loads((P/'copied-scalar-replay.json').read_text())
original=json.loads((P/'inputs/root-review/new-cut-conditional-check.json').read_text())
assert copied==original
for label,margin in {'low_cap':cap_margin,'middle_left':value(mid_gap,a),
                     'middle_right':value(mid_gap,b),'middle_concavity':-mid_gap[2],
                     'upper_leading':A,'upper_discriminant':delta}.items():
    assert F(copied['margins'][label])==margin

# Bounded signed-deficit control, unlike the root's unbounded g=-1 toy.
# This remains an algebraic control, not an actual graphon or certificate audit.
kappa=F(2,25);prob=F(1);minimum=F(-1,25);floor=F(1);total=F(2)
weighted=total*minimum
assert -kappa*prob<=minimum<0
assert weighted<floor*minimum
corrected=weighted+kappa*(total-floor)*prob
assert floor*minimum<=corrected

result={
 'scope':'Conditional scalar implication only; no acceptance of arXiv:2606.28041v1 or a new graph theorem.',
 'input_hashes':{str(f.relative_to(P/'inputs')):hashlib.sha256(f.read_bytes()).hexdigest()
                 for f in sorted((P/'inputs').rglob('*')) if f.is_file()},
 'copied_replay_matches':True,
 'coefficients':{'middle_gap':list(map(str,mid_gap)),'upper_gap':list(map(str,upper_gap))},
 'checks':{'cap_positive':True,'middle_concavity_and_endpoints':True,
           'middle_chord_identity':True,'upper_complete_square_identity':True,
           'closed_interval_coverage':'[1/2,a], [a,4/5], [4/5,1]',
           'completion_available':'a>3/4; no use below the known completion threshold',
           'delta_threshold_to_I':True},
 'signed_deficit_control':{'minimum':str(minimum),'type_probability':str(prob),
   'total_weight':str(total),'weight_floor':str(floor),'weighted_deficit':str(weighted),
   'floor_times_minimum':str(floor*minimum),'with_safe_excess_correction':str(corrected),
   'conclusion':'A weight lower bound alone fails for negative deficits. Equality of weights or a justified excess correction is needed. This is not a paper refutation.'},
 'all_checks_pass':True}
(P/'independent-scalar-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'all_checks_pass':True,'conditional_R':str(R),'external_premise_accepted':False}))
