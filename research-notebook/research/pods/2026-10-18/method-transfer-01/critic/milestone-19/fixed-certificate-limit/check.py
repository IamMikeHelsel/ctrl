#!/usr/bin/env python3
from fractions import Fraction as F
from pathlib import Path
import json
w=(F(51,50),F(101,100),F(1)); W=w[0]; floor=F(9,200)
e=tuple(F(n,10**8) for n in (101533,368033,1042283))
def policy(m):
 x,v,a=m;A=(x,x+v/4,x+v/2+a/16)
 K=max([floor]+[(A[i]-A[j]+e[i]+e[j])/(w[i]+w[j]) for i in range(3) for j in range(3)])
 lo=max(A[i]+e[i]-w[i]*K for i in range(3));hi=min(A[i]-e[i]+w[i]*K for i in range(3))
 assert lo<=hi and all(abs(A[i]-lo)+e[i]<=w[i]*K for i in range(3))
 return A,K,lo,hi
cases=[]
readings=[(F(7,50),-F(1,100),-F(117,100)),(F(143,1000),F(561,50000),-F(127,100)),(F(-2),F(3),F(4))]
for m in readings:
 A,K,c,hi=policy(m);U=c+W*K
 for increment in [F(0),F(1,10000),F(1,10),F(2)]:
  kp=K+increment;cp=max(A[i]+e[i]-w[i]*kp for i in range(3))
  assert all(abs(A[i]-cp)+e[i]<=w[i]*kp for i in range(3))
  assert cp+W*kp>=U
 cases.append({'m':[str(z) for z in m],'K':str(K),'left':str(c),'right':str(hi),'optimum':str(U)})
A,K,c,hi=policy(readings[0]);assert hi>c and (c+hi)/2+W*K>c+W*K
assert cases[1]['optimum']=='3013722449/20100000000'
# Essential sign failure in the generalization W<w.
assert abs(F(-2))<=2*1 and abs(F(-4))<=2*2
assert -4+1*2 < -2+1*1
# A diagonal pair is required when one interval has positive error.
assert (0-0+1+1)/(F(1)+1)==1
assert not abs(F(0)-0)+1<=F(1)*0
out={'scope':'Examples and falsifiers only; general proof is written algebra, not finite testing','cases':cases,'nominal_midpoint_strictly_worse':True,'W_below_weight_counterexample':{'w':'2','W':'1','K0':'1','first':{'K':'1','c':'-2','U':'-1'},'better':{'K':'2','c':'-4','U':'-2'}},'diagonal_pair_omission_fails':True,'all_checks_pass':True}
(Path(__file__).parent/'result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
