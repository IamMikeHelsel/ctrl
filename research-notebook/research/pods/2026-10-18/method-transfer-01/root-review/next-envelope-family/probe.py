"""Small numerical proposal check only; not an all-time bound or acceptance."""
from pathlib import Path
import math,json
T=.05;V=.41;A=.1;b=1.2;k=8;X=.001
xT=X+V*T+A*T*T/2;vT=V+A*T
def x(s):return xT+vT*s-b*s*s/2+(A+b)*(s/k-(1-math.exp(-k*s))/(k*k))
def v(s):return vT-b*s+(A+b)*(1-math.exp(-k*s))/k
lo,hi=0.,.48
for _ in range(80):
 mid=(lo+hi)/2
 if v(mid)>0:lo=mid
 else:hi=mid
s=(lo+hi)/2
out={'scope':'Floating-point proposal on a single constant-rate envelope; not a certified maximum or an accepted smaller guard','recovered_zero_estimate':s,'absolute_zero_estimate':T+s,'position_at_estimated_zero':x(s),'simple_envelope_bound':xT+(vT+(A+b)/k)**2/(2*b),'accepted_old_ceiling':.142,'hypothesis':'A reusable whole-envelope certificate might retain more clearance than the current three-interval bound. Do not change C5/C6 from this calculation.'}
Path(__file__).with_name('probe-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
