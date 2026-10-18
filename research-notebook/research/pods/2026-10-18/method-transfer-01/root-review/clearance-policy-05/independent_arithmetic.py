"""Independent exact reconstruction; imports no builder code. Finite affine
extrema supplement the inspected universal Lean proof, not a simulation."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
P=Path(__file__).resolve().parent
w=(F(51,50),F(101,100),F(1)); target=F(9,200); drift=F(3,1700)
A=F(33,25); V=F(3,100)+A/2000; J=12*(F(121,100)+F(1,100)+A)
e=(F(1,1000)+V/2000,F(1,100)+A/2000,F(1,20)+J/2000)
E=(e[0],e[0]+e[1]/4,e[0]+e[1]/2+e[2]/16)
assert E==tuple(F(x,10**8) for x in (101533,368033,1042283))

def offsets(m):
 x,v,a=m;return(x,x+v/4,x+v/2+a/16)
def policy(m):
 a=offsets(m); candidates=[target]+[(a[i]-a[j]+E[i]+E[j])/(w[i]+w[j]) for i,j in product(range(3),repeat=2)]
 K=max(candidates); c=max(a[i]+E[i]-w[i]*K for i in range(3))
 assert all(abs(a[i]-c)+E[i]<=w[i]*K for i in range(3))
 return c,K,c+w[0]*K
corners=[(F(143,1000),v,a) for v,a in product((F(-561,50000),F(561,50000)),(F(-127,100),F(-1,5)))]
rows=[]; affine=[]
for m in corners:
 a=offsets(m); candidates=[target]+[(a[i]-a[j]+E[i]+E[j])/(w[i]+w[j]) for i,j in product(range(3),repeat=2)]
 c,K,U=policy(m);rows.append({'reading':m,'center':c,'radius':K,'upper':U})
 affine.extend(a[i]+E[i]+(w[0]-w[i])*k for i,k in product(range(3),candidates))
U=max(affine);Kmax=max(r['radius'] for r in rows)
assert len(affine)==120 and U==F(3013722449,20100000000)
assert Kmax==F(2407079,50250000) and max(w)*Kmax<F(2221,40000)
assert U==max(r['upper'] for r in rows)
# U is a maximum of thirty affine functions. Their x coefficient is one,
# so x<=.143 reduces the unbounded rectangle to its upper x face.
# Their v/a maxima on this rectangle occur at its four corners.
slopes=[-8*v-6*a-F(r,2)*(-F(121,100)+d-a) for v,a,r,d in product((-V,V),(-A,A),(8,12),(F(-1,100),F(1,100)))]
assert min(slopes)==F(11967,6250) and max(slopes)==F(48533,6250)<8
nom=(F(7,50),F(-1,100),F(-117,100));c,K,Unom=policy(nom)
assert (c,K,Unom)==(F(9573033,10**8),target,F(14163033,10**8))
old=F(323,3200);a=offsets(nom);oldK=max([target]+[(abs(a[i]-old)+E[i])/w[i] for i in range(3)])
oldU=old+w[0]*oldK
assert oldK==F(4948533,10**8) and oldU==F(757062683,5000000000)>F(3,20)
newcmd=-8*(nom[0]-c)-6*nom[1]-nom[2]/2
assert newcmd==F(3635533,12500000)
# Inspect all weighted face extremes for K=target. Multi-affinity gives
# box extremes; for arbitrary K>=target the coefficients below are <=0.
face_rows=[]
for i in range(3):
 for r in (F(8),F(12)):
  for signs in product((-1,1),repeat=3):
   for residual in (F(-111,1000),F(111,1000)):
    def face(k):
     z=[signs[j]*w[j]*k for j in range(3)]
     f=(4*(-z[0]+z[1]),4*(-z[1]+z[2]),4*((1-r/8)*z[0]+3*(r/8-1)*z[1]+(2-3*r/8)*z[2])+r*residual/16)
     return signs[i]*f[i]+w[i]*drift
    val=face(target);coefficient=face(target+1)-val
    assert val<=0 and coefficient<=0
    face_rows.append((i,r,signs,residual,val,coefficient))
wide=policy((F(143,1000),F(1,50),F(-127,100)))[2]
assert wide==F(15213033,10**8)>F(3,20)
assert F(111,1000)>2*target
out={'scope':'Exact policy and face reconstruction, no builder imports or trajectory claims',
 'startup':{'A':A,'V':V,'J':J,'measurement_errors':e,'coordinate_errors':E},
 'guard_corners':rows,'affine_values_checked':len(affine),'upper':U,'margin':F(3,20)-U,
 'Kmax':Kmax,'guard_duration':(Kmax-target)/drift,'pending_slope_extrema':(min(slopes),max(slopes)),
 'weighted_face_checks':len(face_rows),'face_maximum':max(t[-2] for t in face_rows),
 'nominal':{'center':c,'radius':K,'upper':Unom,'command':newcmd,'retreat':nom[0]-c},
 'same_errors_old_center':{'radius':oldK,'upper':oldU},
 'negative_controls':{'wider_speed_upper':wide,'small_cube_invalid':True},'passed':True}
(P/'arithmetic-result.json').write_text(json.dumps(out,default=str,indent=2)+'\n')
print('Independent exact arithmetic passed:',len(affine),'affine values,',len(face_rows),'face cases')
