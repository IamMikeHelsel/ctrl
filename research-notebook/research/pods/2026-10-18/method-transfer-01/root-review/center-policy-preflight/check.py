"""Exact algebraic preflight only; no execution, existence or Lean claim."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent
D=F(1,2000);R=F(2221,40000);weights=[F(51,50),F(101,100),F(1)]
A=F(127,100)+F(1,20);V=F(1,50)+F(1,100)+A*D;J=12*(F(122,100)+A)
e=[F(1,1000)+V*D,F(1,100)+A*D,F(1,20)+J*D]
slope=[-8*v-6*a-r*(-F(121,100)+d-a)/2 for v,a,r,d in product([-V,V],[-A,A],[F(8),F(12)],[-F(1,100),F(1,100)])]
assert max(map(abs,slope))<8

def geometry(m,alpha):
 x,v,a=m;c=x+v/4+alpha*a
 center=[x-c,x-c+v/4,x-c+v/2+a/16]
 errors=[e[0],e[0]+e[1]/4,e[0]+e[1]/2+e[2]/16]
 budget=[abs(z)+b for z,b in zip(center,errors)]
 rho=max(b/w for b,w in zip(budget,weights))
 return {'center':c,'startup_abs_budgets':budget,'startup_weighted_radius':rho,
 'proposed_position_upper_if_weighted_comparison_is_proved':c+weights[0]*max(F(45,1000),rho),
 'startup_position_upper':x+e[0]}

rows=[]
for alpha in [F(1,32),F(1,28)]:
 guard_budgets=[e[0]+F(1,50)/4+alpha*F(127,100),e[0]+e[1]/4+alpha*F(127,100),e[0]+e[1]/2+e[2]/16+F(1,50)/4+abs(F(1,16)-alpha)*F(127,100)]
 nominal=geometry([F(14,100),-F(1,100),-F(117,100)],alpha)
 candidates=[(v,a,geometry([F(143,1000),v,a],alpha)) for v,a in product([-F(1,50),F(1,50)],[-F(127,100),-F(11,10)])]
 worst=max(candidates,key=lambda z:z[2]['proposed_position_upper_if_weighted_comparison_is_proved'])
 rows.append({'alpha':alpha,'guard_acceleration':F(127,100),'whole_guard_startup_budgets':guard_budgets,'old_cube_startup_pass':max(guard_budgets)<=R,'nominal':nominal,'rectangle_corner_worst':{'measured_v':worst[0],'measured_a':worst[1],**worst[2]}})
assert rows[1]['old_cube_startup_pass']
assert rows[1]['nominal']['proposed_position_upper_if_weighted_comparison_is_proved']<F(15,100)
assert rows[1]['rectangle_corner_worst']['proposed_position_upper_if_weighted_comparison_is_proved']>F(15,100)

def encode(o):
 if isinstance(o,F):return {'rational':str(o),'decimal':float(o)}
 raise TypeError(type(o))
result={'scope':'Algebraic proposal screen, not a trajectory certificate. New center and guard require new source proof; original C3 is unchanged. Proposed weighted envelope requires a variable-initial-radius theorem. No detector or execution existence inferred.','startup':{'A':A,'V':V,'J':J,'error_envelopes':e,'slope_min':min(slope),'slope_max':max(slope)},'cases':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(p/'result.json').write_text(json.dumps(result,default=encode,indent=2)+'\n')
for row in rows: print('alpha',row['alpha'],'nominal proposed upper',float(row['nominal']['proposed_position_upper_if_weighted_comparison_is_proved']),'rectangle corner upper',float(row['rectangle_corner_worst']['proposed_position_upper_if_weighted_comparison_is_proved']))
