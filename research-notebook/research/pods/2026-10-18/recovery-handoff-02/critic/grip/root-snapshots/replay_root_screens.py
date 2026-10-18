#!/usr/bin/env python3
"""Check recorded arithmetic and illustrative flow values. Does not run Lean."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json,math

HERE=Path(__file__).resolve().parent
bridge=json.loads((HERE/'root-braking-bridge-screen.json').read_text())
q=-F(121,100)
corners=[abs(-8*v-6*a-r*(q+d-a)/2) for v,a,r,d in product(
 [-F(1061,50000),F(1061,50000)],[-F(61,50),F(61,50)],[F(8),F(12)],[-F(1,100),F(1,100)])]
assert max(corners)==F(bridge['box_max_absolute_feedback_slope']['abs'])==F(46811,6250)
assert F(bridge['slack'])==F(2221,20000)-(F(103,1000)+F(8,1000))==F(1,20000)
old=json.loads((HERE/'root-arithmetic-screen.json').read_text())['grip_same_contract_as_old_stopping_certificate']
x,v,A,T,b,lam=[F(old[k]['exact']) for k in ('xHi','vHi','A','T','b','lambda')]
L=x+v*T+A*T*T/2+(v+A*T+(A+b)/lam)**2/(2*b)
assert L==F(old['simple_position_bound']['exact'])==F(4111,25600)>F(3,20)
for row in json.loads((HERE/'root-conservatism-screen.json').read_text())['rows']:
 v,A,T,b,lam=[F(row[k]) for k in ('v0','A','T','b','lambda')]
 assert v*T+A*T*T/2+(v+A*T+(A+b)/lam)**2/(2*b)==F(row['distance_bound_m'])
reach=json.loads((HERE/'root-admission-reachability-screen.json').read_text())
for row in reach['rows']:
 rate=row['r']
 def state(s):
  e=math.exp(-rate*s)
  return (.021625+.415*s-1.2*s*s/2+1.3*(s/rate-(1-e)/rate**2),
          .415-1.2*s+1.3*(1-e)/rate,-1.2+1.3*e)
 for key,tkey,target in [('first_zero_state','first_zero_time_s',0),('v_minus_0_01_state','v_minus_0_01_time_s',-.01)]:
  actual=state(row[tkey]-.05)
  assert all(abs(a-z)<1e-13 for a,z in zip(actual,row[key]))
  assert abs(actual[1]-target)<1e-13
 assert row['peak_below_fixed_admission_minimum_0_139']==(row['first_zero_state'][0]<.139)
fig=json.loads((HERE/'figures/figure-provenance.json').read_text())
assert hashlib.sha256((HERE/'figures/make_figures.py').read_bytes()).hexdigest()==fig['script_sha256']
for name,digest in fig['files'].items():
 assert hashlib.sha256((HERE/'figures'/name).read_bytes()).hexdigest()==digest
print(json.dumps({'passed':True,'scope':'Exact rational checks, binary64 formula consistency and figure identity. This is not Lean replay, interval validation, or hardware evidence.'},indent=2))
