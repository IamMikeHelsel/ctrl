#!/usr/bin/env python3
"""Exact independent algebra for the frozen four-box contract, without plant runs."""
from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[5]
CERT=HERE.parent.parent/'certificate-03/builder'
INTENT=HERE.parent.parent/'intent-contract-07/analyst'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def value(n,z):
 return sum((-1)**i*comb(4,i)*max(z-i,F(0))**n for i in range(5))/factorial(n)
def polynomial(n,k):
 # Local coordinate u=z-k on the closed cell[k,k+1]. The next term is zero at u=1.
 return [sum(F((-1)**i*comb(4,i)*comb(n,j)*(k-i)**(n-j),factorial(n)) for i in range(k+1)) for j in range(n+1)]
def bernstein(power):
 n=len(power)-1
 return [sum(power[k]*F(comb(i,k),comb(n,k)) for k in range(i+1)) for i in range(n+1)]
def strings(xs):return list(map(str,xs))
rows=[]
for k in range(4):
 p=polynomial(4,k);dp=polynomial(3,k)
 assert [i*p[i] for i in range(1,5)]==dp
 bp,bdp=bernstein(p),bernstein(dp)
 assert min(bp)>=0 and max(bp)<=1 and min(bdp)>=0
 rows.append({'cell':[k,k+1],'F0_power':strings(p),'F0_bernstein':strings(bp),
   'F1_power':strings(dp),'F1_bernstein':strings(bdp)})
assert value(4,F(2))==F(1,2) and value(4,F(4))==1
assert [value(1,F(i)) for i in range(5)]==[0,1,-2,1,0]
h=F(1,5);tau=F(11,50);delta=F(1,50);R=F(1,5000)
assert delta*value(4,(F(31,50)-tau)/h)==F(1,100)
assert delta*value(4,(F(51,50)-tau)/h)==delta
assert 2*delta/h**3==5<=F(15,2)
assert F(1,100)-R==F(49,5000)>R
q_future=lambda t:delta*value(4,(t-1)/h)
assert all(value(n,F(-5))==0 for n in range(1,5))
assert q_future(F(0))==0 and q_future(F(9,5))==delta
# The global error cube contains a point that fails both full endpoint limits.
corner=(R,-F(2,125),F(32,25))
cube=(corner[0],corner[0]+corner[1]/40,corner[0]+corner[1]/20+corner[2]/1600)
assert max(map(abs,cube))==R and abs(corner[1])>F(1,1000) and abs(corner[2])>F(1,50)
# Persistent bounded disturbance can sustain nonzero motion under the stated plant.
# q=0, r=100, x=e*sin(t), v=e*cos(t), a=-e*sin(t).
# u=-799.5e*sin(t)-60e*cos(t). Choose w=798.5e*sin(t)+59.99e*cos(t).
eps=F(1,10**6);u_sin=-F(1599,2)*eps;u_cos=-60*eps
w_sin=F(1597,2)*eps;w_cos=F(5999,100)*eps
assert 100*(u_sin+w_sin+eps)==0
assert 100*(u_cos+w_cos)==-eps
assert abs(w_sin)+abs(w_cos)<F(1,100)
frozen={}
for folder in (CERT,INTENT):
 m=folder/'artifact-sha256.json';data=json.loads(m.read_text())
 files=data.get('files',data)
 for name,info in files.items():
  want=info['sha256'] if isinstance(info,dict) else info
  assert sha(folder/name)==want,(folder,name)
 frozen[str(folder.relative_to(WORK))]={'manifest_sha256':sha(m),'files':len(files)}
out={'passed':True,'method':'Exact rational independent cell expansion and Bernstein coefficients; not a plant simulation or a substitute for Lean.',
 'four_box_cells':rows,'midpoint':'1/2','jerk_knot_values':['0','1','-2','1','0'],
 'fixed_step':{'midpoint_time_s':str(tau+2*h),'midpoint_reference_m':'1/100','directed_progress_lower_m':str(F(1,100)-R),
 'arrival_time_s':str(tau+4*h),'reference_peak_jerk_m_s3':'5','sufficient_deadline_not_necessary_for_every_physical_trajectory':True},
 'pending_event':{'event':['1','1/50'],'current_time':'0','current_reference_jet':['0','0','0','0'],
 'later_time':'9/5','later_reference_m':'1/50','zero_current_derivatives_do_not_imply_complete_history':True},
 'endpoint_corner':{'state':strings(corner),'transformed':strings(cube),'speed_limit':'1/1000','acceleration_limit':'1/50',
 'scope':'The cube implication fails; this is not a numerical endpoint failure of the fixed run.'},
 'persistent_motion_counterexample':{'q':'0','rate':'100','x':'1e-6*sin(t)','v':'1e-6*cos(t)','a':'-1e-6*sin(t)',
 'w_sin_coefficient':str(w_sin),'w_cos_coefficient':str(w_cos),'disturbance_upper_bound':str(abs(w_sin)+abs(w_cos)),
 'plant_coefficient_identity_verified':True,'nonzero_velocity_times':'t=2*pi*n for every nonnegative integer n',
 'scope':'Analytic coefficient and magnitude check, not a Lean-certified trajectory. Shows bounded disturbance is not a finite-rest assumption.'},
 'frozen_inputs':frozen}
(HERE/'contract-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'cells':len(rows),'frozen_inputs':frozen},indent=2))
