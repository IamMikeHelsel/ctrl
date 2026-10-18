#!/usr/bin/env python3
from fractions import Fraction as F
import json
from pathlib import Path
p=Path(__file__).resolve().parent
v=json.loads((p/'preflight-results.json').read_text())['scalar_obstruction'];y=F(v['y']);j=F(v['j']);mu=2*j/y;b=y-F(1,2);R=F(2586,100000)
L=8*R*(y-mu)-2*mu;C=j-4*R*(y-mu)**2-mu**2;B=(j-R)/b-L;S=B*B/4+L*mu-C
regular=F(json.loads((p/'preflight-results.json').read_text())['regular_neighborhood_screen']['cost'])
# The kink condition fails for both bounds. The actual-mean tangent still works.
concavity_regular=j<=regular*(4*y-1)
concavity_target=j<=R*(4*y-1)
assert not concavity_regular and not concavity_target
assert C<0 and S<=0
# Exact polynomial identities on representative rationals; coefficients are also
# recorded explicitly for independent symbolic checking.
for d in [F(0),b,mu,y,F(1,7),F(2,9)]:
 low=j-4*R*(y-d)**2-d*d
 high=(j-R)*d/b-d*d
 assert low==C+L*(d-mu)-(4*R+1)*(d-mu)**2
 assert high-(C+L*(d-mu))==-(d-B/2)**2+S
out={'scope':'Exact arithmetic for a proposed moment certificate at one density pair; not a uniform graph theorem','R':str(R),'y':str(y),'j':str(j),'mean_degree':str(mu),'tangent_slope':str(L),'tangent_at_mean':str(C),'upper_branch_linear_coefficient':str(B),'upper_branch_square_remainder':str(S),'checks':{'C_negative':C<0,'upper_branch_remainder_nonpositive':S<=0,'global_concavity_at_regular_bound':concavity_regular,'global_concavity_at_target_bound':concavity_target},'formulas':{'low':'phi(d)=j-4R(y-d)^2-d^2; phi(d)=C+L(d-mu)-(4R+1)(d-mu)^2','high':'phi(d)=(j-R)d/b-d^2; phi(d)-(C+L(d-mu))=-(d-B/2)^2+S','moment':'E[d]=2j/y and E[s]=E[d^2]; if all neighborhood candidates exceed R then E[phi]>0, but tangent certificate gives E[phi]<=C<0'}}
(p/'point-moment-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'C':float(C),'S':float(S),'global_concavity':concavity_target,'tangent_check':True},indent=2))
