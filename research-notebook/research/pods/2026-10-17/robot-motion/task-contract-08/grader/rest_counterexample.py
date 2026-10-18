#!/usr/bin/env python3
"""Exact Fourier coefficient identity for a rest-starting persistent motion."""
from fractions import Fraction as F
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
# Dictionary (harmonic, trig): coefficient, in units of eps=10^-6.
x={(0,'c'):F(5,2),(1,'c'):-F(15,4),(2,'c'):F(3,2),(3,'c'):-F(1,4)}
def derivative(p):
 out={}
 for (n,k),v in p.items():
  if n:out[(n,'s' if k=='c' else 'c')]=(-n if k=='c' else n)*v
 return out
def linear(*terms):
 out={}
 for mult,p in terms:
  for key,v in p.items():out[key]=out.get(key,0)+mult*v
 return {key:v for key,v in out.items() if v}
v=derivative(x);a=derivative(v);j=derivative(a)
u=linear((-800,x),(-60,v),(-F(1,2),a))
w=linear((F(1,100),j),(1,a),(-1,u))
assert linear((100,u),(100,w),(-100,a))==j
at0=lambda p:sum(v for (n,k),v in p.items() if k=='c')
assert at0(x)==at0(v)==at0(a)==0
# q=0, j_ref=0, r=100; initial transformed error is therefore exactly zero.
eps=F(1,10**6);bound=sum(map(abs,w.values()))*eps
assert bound<F(1,100)
# v(pi/2+2*pi*n)=3*eps, for every integer n>=0.
assert v[(1,'s')]-v[(3,'s')]==3
formatp=lambda p:{str(n)+k:str(v) for (n,k),v in p.items()}
out={'passed':True,'reference':'q=0; all reference derivatives zero','rate':'100',
 'epsilon':'1/1000000','x':'epsilon*(1-cos(t))^3',
 'position_coefficients_over_epsilon':formatp(x),'input_coefficients_over_epsilon':formatp(u),
 'disturbance_coefficients_over_epsilon':formatp(w),'initial_x_v_a':['0','0','0'],
 'disturbance_absolute_upper_bound':str(bound),'disturbance_limit':'1/100',
 'nonzero_velocity':'3*epsilon at pi/2+2*pi*n for every nonnegative integer n',
 'plant_identity':'a_prime = 100*(u+w-a)',
 'scope':'Analytic Fourier coefficient proof, not a Lean trajectory theorem. A bounded disturbance need not permit exact finite-time physical rest, even from exact rest.'}
(HERE/'rest-counterexample.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
