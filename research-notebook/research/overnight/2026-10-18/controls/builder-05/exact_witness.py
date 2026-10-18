"""Exact illustrative witness values; finite checks are not an all-time proof."""
from fractions import Fraction as F
from pathlib import Path
import json, math
HERE=Path(__file__).resolve().parent
h=F(1,5);events=[(F(11,50),F(1,50)),(F(31,50),F(-1,50))]
def ref(t,k):
 return sum(d/h**k/math.factorial(4-k)*sum((-1)**m*math.comb(4,m)*max((t-tau)/h-m,0)**(4-k) for m in range(5)) for tau,d in events)
def row(t,b,changing):
 q,v,a,j=(ref(t,k) for k in range(4));x=q+b/800
 r=(F(92) if t<=F(1,2) else F(100)) if changing else F(96)
 w=b+j*(1/r-F(1,96)) if changing else b
 u=a-800*(x-q)-60*(v-v)-(a-a)/2+j/96
 assert r*(u+w-a)==j
 assert abs(w)<=F(1,100)
 assert [x-q,x-q+(v-v)/40,x-q+(v-v)/20+(a-a)/1600]==[b/800]*3
 return {'t_s':str(t),'reference_x_m':str(q),'actual_x_m':str(x),'actual_v_m_per_s':str(v),'actual_a_m_per_s2':str(a),'actual_j_m_per_s3':str(j),'response_per_s':str(r),'disturbance_m_per_s2':str(w),'command_m_per_s2':str(u),'physical_ode_identity':True}
points=[F(0),F(11,50),F(1,2),F(5001,10000),F(31,50),F(71,50),F(171,50),F(4)]
res={name:[row(t,b,changing) for t in points] for name,b,changing in [('constant_bias',F(1,100),False),('changing_inputs',F(1,200),True)]}
assert ref(F(1,2),0)==F(779,250000)
assert ref(F(1,2),1)==F(311,7500)
assert row(F(71,50),F(1,100),False)['actual_x_m']=='1/80000'
(HERE/'exact-witness-values.json').write_text(json.dumps({'scope':'16 exact rational anchor evaluations of the explicitly constructed witness; Lean supplies the global derivative and trajectory statements.','rows':res},indent=2)+'\n')
print('16 exact witness anchor states and ODE identities passed')
