#!/usr/bin/env python3
"""Read-only rational replay. Does not import or run the generator."""
from fractions import Fraction as Q
from pathlib import Path
import json

data=json.loads((Path(__file__).resolve().parent/'comparison.json').read_text())
r,i,a,h=Q(323,12500),Q(2,47),Q(779,1000),Q(783,1000)
assert [Q(data[k]) for k in ['R','I','a','h']]==[r,i,a,h]
assert data['cover']==[
 {'c':['1/2','779/1000'],'bound':'I*c^2'},
 {'c':['779/1000','783/1000'],'bound':'I*h^2-64*a^5*(1-h)*I^3'},
 {'c':['783/1000','4/5'],'bound':'old combined first branch'},
 {'c':['4/5','1'],'bound':'old combined second branch'}]
assert Q(1,2)<a<h<Q(4,5)<1
assert Q(3,4)<Q(7797,10000)<h
polynomial=lambda c:(r-i-Q(17,32))*c*c+Q(7,8)*c+r-Q(3,8)
aa,dd,ee=r+Q(1,4)-i,Q(3,8),r+Q(1,8)
window=i*h*h-64*a**5*(1-h)*i**3
expected={
 'comparison_improvement':Q(1293,50000)-r,
 'low_cap':r-i*a*a,'window_cap':r-window,'j_monotonicity':1-48*i*i,
 'middle_left':polynomial(h),'middle_right':polynomial(Q(4,5)),
 'middle_concavity':-(r-i-Q(17,32)),'upper_leading':aa,
 'upper_discriminant':4*aa*ee-dd*dd,'old_threshold_gap':h-Q(7797,10000)
}
assert {k:Q(v) for k,v in data['margins'].items()}==expected
assert all(v>0 for v in expected.values())
assert Q(data['window_upper'])==window
point=data['old_obstruction'];c,j,y=map(Q,[point['c'],point['j'],point['y']])
mu=j/y**2; alpha=min(c,1-c); ell=min(4*alpha**2,alpha*(1-alpha))
saving=4*ell*mu**3*y**2
assert 2*c*y==1 and saving==64*ell*c**4*j**3
assert Q(point['saving'])==saving and Q(point['old_beta'])==c*c*j
assert Q(point['improved_cap'])==c*c*j-saving<r
assert Q(point['margin_below_R'])==r-(c*c*j-saving)>0
assert Q(point['omitting_y_squared_overstates_saving_by_factor'])==1/y**2>1
neg=data['negative_controls'];sr=Q(neg['unchanged_split_at_smaller_target']['target'])
assert (sr-i-Q(17,32))*h*h+Q(7,8)*h+sr-Q(3,8)==Q(neg['unchanged_split_at_smaller_target']['middle_left_margin'])<0
radius=neg['wrong_radius_min_branch'];rc,rd=Q(radius['c']),Q(radius['degree'])
plus=min((1-rc)/(1-rd),rc/rd);minus=min(rc/(1-rd),(1-rc)/rd)
assert Q(radius['product'])==plus*minus<Q(radius['incorrect_lower_bound'])
assert Q(radius['valid_L'])<=plus*minus
assert Q(neg['old_scalar_only']['beta_minus_E1_R'])==c*c*j-Q(1293,50000)>0
print(json.dumps({'passed':True,'four_regions_cover_full_domain':True,
                  'all_exact_margins_positive':True,'negative_controls_confirmed':3,
                  'conclusion':'Cited cubic lemma plus unchanged completion/BCL bound yields.02584; no new formal endpoint.'},indent=2))
