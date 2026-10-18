"""Floating-point diagnostics only. Closed-form ZOH flow, no numerical ODE solver.
Root bisection is numerical evidence, NOT interval-certified or Lean-verified.
"""
import math,json
from pathlib import Path

def flow(x,v,a,u,t,tau):
 e=math.exp(-t/tau)
 return (x+v*t+u*t*t/2+(a-u)*tau*(t-tau*(1-e)),
         v+u*t+(a-u)*tau*(1-e),u+(a-u)*e)

def brake(v,a,tau,U=1):
 # v>=0,a>=-U; unique positive zero if v>0 (otherwise handle immediate maximum).
 if v<=0 and a<=0:return {'time':0.,'distance':0.}
 lo=0.;hi=max(1.,(v+(a+U)*tau)/U)
 for _ in range(100):
  mid=(lo+hi)/2
  if flow(0,v,a,-U,mid,tau)[1]>0:lo=mid
  else:hi=mid
 t=(lo+hi)/2
 return {'time':t,'distance':flow(0,v,a,-U,t,tau)[0]}

def delayed(v,a,tau,delay,U=1):
 x1,v1,a1=flow(0,v,a,U,delay,tau)
 # Include a possible early local maximum during reaction when a starts negative.
 reaction_peak=max(0.,x1)
 if a<0 and v>0:
  turn=min(delay,tau*math.log((U-a)/U))
  if flow(0,v,a,U,turn,tau)[1]<0:
   lo,hi=0.,turn
   for _ in range(100):
    mid=(lo+hi)/2
    if flow(0,v,a,U,mid,tau)[1]>0:lo=mid
    else:hi=mid
   reaction_peak=max(reaction_peak,flow(0,v,a,U,(lo+hi)/2,tau)[0])
 # This bounded diagnostic skips negative velocity at the braking handoff.
 if v1<0:return None
 b=brake(v1,a1,tau,U)
 return {'total_distance':max(reaction_peak,x1+b['distance']),'delay_end':[x1,v1,a1],**b}
rows=[]
for v,a,d in [(1,1,0),(1,0,0),(1,1,.2),(1,0,.2)]:
 row={'v':v,'a':a,'delay':d,'tau':1,'naive':v*v/2,**delayed(v,a,1,d)}
 rows.append(row)
# Probe the invalid shortcut "largest lag is always worst even during reaction".
found=[]
for a in [-1,-.5,0,.5,1]:
 for v in [.1,.5,1,2]:
  for d in [.2,.5,1,2,5]:
   vals=[delayed(v,a,tau,d)for tau in [.25,.5,1,2]]
   if all(vals)and max(r['total_distance']for r in vals[:-1])>vals[-1]['total_distance']+1e-8:
    found.append({'v':v,'a':a,'delay':d,'tau_grid':[.25,.5,1,2],'distances':[r['total_distance']for r in vals]})
report={'scope':'numerical diagnostic, not interval-certified or Lean proof','counterexample':'U=tau=v0=a0=1, delay=0, x(1)=1/2+2/e > 1/2 naive guard','examples':rows,'largest_tau_delay_shortcut_counterexamples':found[:5]}
p=Path(__file__).with_name('results.json');p.write_text(json.dumps(report,indent=2)+'\n');print(p.read_text())
