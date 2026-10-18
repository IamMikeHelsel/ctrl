#!/usr/bin/env python3
"""Conservative exact composition of existing cubic and completion bounds."""
from fractions import Fraction as F
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
I=F(2,47); R=F(323,12500); a=F(779,1000); h=F(783,1000)
old_target=F(1293,50000)
def ell(c):
    r=min(c,1-c)
    return min(4*r*r,r*(1-r))
def cap(c,j):
    return c*c*j-64*ell(c)*c**4*j**3
def middle(c,target=R):
    return (target-I-F(17,32))*c*c+F(7,8)*c+target-F(3,8)

window=I*h*h-64*a**5*(1-h)*I**3
A=R+F(1,4)-I;D=F(3,8);E=R+F(1,8)
margins={
    'comparison_improvement':old_target-R,
    'low_cap':R-I*a*a,
    'window_cap':R-window,
    'j_monotonicity':1-48*I*I,
    'middle_left':middle(h),
    'middle_right':middle(F(4,5)),
    'middle_concavity':-(R-I-F(17,32)),
    'upper_leading':A,
    'upper_discriminant':4*A*E-D*D,
    'old_threshold_gap':h-F(7797,10000)
}
assert all(z>0 for z in margins.values())
assert F(1,2)<a<h<F(4,5)<1
assert F(3,4)<h and F(7797,10000)<h

# Same exact old scalar obstruction; the saving is much larger than .00001.
c=F(7797,10000); j=F(2172228946875000,51047928060481223)
beta=F(6256019367,241832986336); y=1/(2*c); mu=j/(y*y)
saving=64*ell(c)*c**4*j**3
assert 4*ell(c)*mu**3*y*y==saving
assert beta==c*c*j and beta>old_target
assert beta-saving<R and saving>F(1,10000)

# A narrower target does not pass this unchanged four-region certificate.
failed_target=F(2583,100000)
failed_margin=middle(h,failed_target)
assert failed_margin<0

# Wrong min branch: at c=.78 and degree delta=.01 the exact feasible radii
# product is smaller than 4(1-c)^2, so that branch cannot be used uniformly.
cc=F(39,50);delta=F(1,100)
tp=min((1-cc)/(1-delta),cc/delta)
tm=min(cc/(1-delta),(1-cc)/delta)
assert tp*tm>=ell(cc) and tp*tm<4*(1-cc)**2

out={
 'status':'exact arithmetic comparison; graph implication uses cited Sarid lemma; no new formal theorem',
 'R':str(R),'previous_E1_R':str(old_target),'I':str(I),'a':str(a),'h':str(h),
 'cover':[
   {'c':['1/2',str(a)],'bound':'I*c^2'},
   {'c':[str(a),str(h)],'bound':'I*h^2-64*a^5*(1-h)*I^3'},
   {'c':[str(h),'4/5'],'bound':'old combined first branch'},
   {'c':['4/5','1'],'bound':'old combined second branch'}],
 'margins':{k:str(v) for k,v in margins.items()},
 'window_upper':str(window),
 'old_obstruction':{'c':str(c),'j':str(j),'y':str(y),'normalized_Y_mu':str(mu),
   'old_beta':str(beta),'saving_L':str(ell(c)),'saving':str(saving),
   'improved_cap':str(beta-saving),'margin_below_R':str(R-(beta-saving)),
   'omitting_y_squared_overstates_saving_by_factor':str(1/(y*y))},
 'negative_controls':{
   'old_scalar_only':{'beta_minus_E1_R':str(beta-old_target),'rejected':True},
   'unchanged_split_at_smaller_target':{'target':str(failed_target),
     'middle_left_margin':str(failed_margin),
     'meaning':'This fixed certificate fails; no scalar optimum or graph counterexample is claimed.'},
   'wrong_radius_min_branch':{'c':str(cc),'degree':str(delta),
     'plus_radius':str(tp),'minus_radius':str(tm),'product':str(tp*tm),
     'incorrect_lower_bound':str(4*(1-cc)**2),'valid_L':str(ell(cc)),
     'meaning':'Replacing min by its first entry overstates the radius guarantee.'}
 }
}
(HERE/'comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'R':str(R),'window_upper':str(window),
                  'old_obstruction_saving_decimal_display':float(saving),
                  'margins':out['margins']},indent=2))
