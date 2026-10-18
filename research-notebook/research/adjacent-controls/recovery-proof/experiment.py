#!/usr/bin/env python3
"""Empirical, deterministic analytic-flow comparison; NOT a formal safety proof.
Only Python's standard library is required. No numerical ODE integrator.
"""
from pathlib import Path
from itertools import product
import argparse,hashlib,json,math,platform

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
P=((38/5,257/25,5),(257/25,1319/50,769/50),(5,769/50,278/25))
T=1.25

def energy(z):return sum(z[i]*P[i][j]*z[j]for i in range(3)for j in range(3))
def command(z):return max(-1.,min(1.,-z[0]-3*z[1]-2*z[2]))
def flow(z,u,t,r):
 x,v,a=z;q=-math.expm1(-r*t)
 return (x+v*t+u*t*t/2+(a-u)*(t/r-q/(r*r)),
         v+u*t+(a-u)*q/r,u+(a-u)*(1-q))

def position_candidates(z,u,h,r):
 """Velocity is monotone on each side of acceleration's possible zero.
 Bisection of its roots finds numerical position extrema, not certified bounds.
 """
 cuts=[0.,h]
 if u and a_diff(z,u):
  ratio=-u/(z[2]-u)
  if 0<ratio<1:
   tc=-math.log(ratio)/r
   if 0<tc<h:cuts.append(tc)
 cuts.sort();out=cuts[:]
 for left,right in zip(cuts,cuts[1:]):
  vl,vr=flow(z,u,left,r)[1],flow(z,u,right,r)[1]
  if vl*vr<0:
   lo,hi=left,right
   for _ in range(60):
    mid=(lo+hi)/2;vm=flow(z,u,mid,r)[1]
    if (vl<0)==(vm<0):lo=mid
    else:hi=mid
   out.append((lo+hi)/2)
 return out

def a_diff(z,u):return z[2]-u

def run(z0,r,mode,hold,horizon,dt):
 segments=[];time=0.;z=tuple(z0);n=0
 if mode=='backup_handoff':
  segments.append((0.,T,z,-1.));z=flow(z,-1.,T,r);time=T
 start=time
 while time<horizon-1e-12:
  end=min(horizon,start+(n+1)*hold);u=command(z)
  segments.append((time,end,z,u));z=flow(z,u,end-time,r);time=end;n+=1
 commands=[s[3]for s in segments]
 samples=[];extrema=[];terminal=None
 for start,end,z,u in segments:
  h=end-start;times={0.,h}
  for k in range(1,math.ceil(h/dt)):times.add(min(h,k*dt))
  if start<=T<=end:times.add(T-start)
  for q in sorted(times):
   state=flow(z,u,q,r);t=start+q;ev=energy(state)
   if abs(t-T)<1e-10:terminal=state
   samples.append((t,state,ev))
  for q in position_candidates(z,u,h,r):extrema.append((start+q,flow(z,u,q,r)[0]))
 peak=max(extrema,key=lambda t:abs(t[1]));xmin=min(x for _,x in extrema);xmax=max(x for _,x in extrema)
 post=[s for s in samples if s[0]>=T-1e-10]
 startV=energy(z0)
 entry=next((s[0]for s in samples if s[2]<=12),None)
 peakV=max(samples,key=lambda s:s[2]);postV=max(post,key=lambda s:s[2])
 switches=sum(abs(b-a)>1e-12 for a,b in zip(commands,commands[1:]))
 return {'mode':mode,'r':r,'initial':list(z0),'initial_V':startV,'phase0_outside_V12':startV>12,
 'terminal_time':T,'terminal_state':list(terminal),'terminal_V':energy(terminal),
 'peak_abs_travel':abs(peak[1]),'peak_travel_time':peak[0],'min_position':xmin,'max_position':xmax,
 'sampled_peak_V':peakV[2],'sampled_peak_V_time':peakV[0],
 'post_T_sampled_peak_V':postV[2],'post_T_sampled_peak_V_time':postV[0],
 'first_sampled_V_le_12_time':entry,'final_state':list(samples[-1][1]),'final_V':samples[-1][2],
 'command_switches':switches,'command_segments':len(segments),
 'command_total_variation':sum(abs(b-a)for a,b in zip(commands,commands[1:])),
 'saturated_duration':sum(b-a for a,b,_,u in segments if abs(u)>=1-1e-12),
 'observed_travel_within_2':max(abs(xmin),abs(xmax))<=2,
 'post_T_observed_V_within_12':postV[2]<=12,
 'trace':list({round(t,12):{'t':t,'x':z[0],'v':z[1],'a':z[2],'V':e}for t,z,e in samples if abs(t*10-round(t*10))<1e-8 or abs(t-T)<1e-8}.values())}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--hold',type=float,default=.1);ap.add_argument('--horizon',type=float,default=20.);ap.add_argument('--dt',type=float,default=.005);args=ap.parse_args()
 assert 0<args.hold<=.2 and args.horizon>T and args.dt>0
 corners=list(product((.99,1.01),(.49,.51),(-.01,.01)))
 runs=[run(z,r,m,args.hold,args.horizon,args.dt)for r in(.9,1.,1.1)for z in corners for m in('direct_feedback','backup_handoff')]
 # Refine the sampling used only for energy peaks; position extrema use root bisection.
 fine=[run(z,r,m,args.hold,args.horizon,args.dt/2)for r in(.9,1.,1.1)for z in corners for m in('direct_feedback','backup_handoff')]
 sensitivity=max(abs(a['post_T_sampled_peak_V']-b['post_T_sampled_peak_V'])for a,b in zip(runs,fine))
 summary={}
 for m in ('direct_feedback','backup_handoff'):
  rr=[x for x in runs if x['mode']==m]
  summary[m]={k:[min(x[k]for x in rr),max(x[k]for x in rr)]for k in ['initial_V','terminal_V','peak_abs_travel','post_T_sampled_peak_V','first_sampled_V_le_12_time','command_switches','command_total_variation','saturated_duration','final_V']}
  summary[m]['observed_travel_violations']=sum(not x['observed_travel_within_2']for x in rr)
  summary[m]['post_T_observed_energy_violations']=sum(not x['post_T_observed_V_within_12']for x in rr)
 differences=[]
 for direct,backup in zip(runs[::2],runs[1::2]):
  differences.append({'r':direct['r'],'initial':direct['initial'],**{k:backup[k]-direct[k]for k in ['terminal_V','peak_abs_travel','post_T_sampled_peak_V','command_switches','command_total_variation']}})
 hold_checks=[]
 for hold in (.05,.1,.2):
  pairs=[(run(z,r,'direct_feedback',hold,args.horizon,args.dt),run(z,r,'backup_handoff',hold,args.horizon,args.dt))for r in(.9,1,1.1)for z in corners]
  hold_checks.append({'hold':hold,'backup_time_aligns_with_baseline_clock':abs(T/hold-round(T/hold))<1e-9,
   'paired_travel_difference_range':[min(b['peak_abs_travel']-a['peak_abs_travel']for a,b in pairs),max(b['peak_abs_travel']-a['peak_abs_travel']for a,b in pairs)],
   'paired_terminal_V_difference_range':[min(b['terminal_V']-a['terminal_V']for a,b in pairs),max(b['terminal_V']-a['terminal_V']for a,b in pairs)],
   'direct_observed_travel_violations':sum(not a['observed_travel_within_2']for a,b in pairs),
   'backup_observed_travel_violations':sum(not b['observed_travel_within_2']for a,b in pairs),
   'direct_terminal_V_range':[min(a['terminal_V']for a,b in pairs),max(a['terminal_V']for a,b in pairs)]})
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 sources={n:sha(ROOT/'lean-controls/LeanControls'/n)for n in ['UncertainLag.lean','UncertainTravel.lean','SaturatedLag.lean','Generated/TravelQuarterLower.lean']}
 out={'status':'empirical analytic-flow illustration; not interval certified or a proof',
 'python':platform.python_version(),'experiment_sha256':sha(Path(__file__)),
 'parameters':{'hold':args.hold,'horizon':args.horizon,'sample_spacing':args.dt,'backup_duration':T,'rates':[.9,1,1.1],'initial_corners':8,'U':1},
 'semantics':'x_prime=v;v_prime=a;a_prime=r*(u-a);fixed r per run. Direct u=clip(-x-3v-2a,-1,1) sampled every hold from time0. Backup holds u=-1 until T then restarts the same sampled feedback clock at T. No state reset.',
 'errors':'zero measurement, quantization, disturbance, command and timing error in both phases; exact model with floating-point evaluation',
 'physical_example_only':'If nominal tau0=.1s, T=1.25 is125ms and horizon20 is2s. All reported states/time are normalized, not calibrated hardware.',
 'metric_notes':{'peak_abs_travel':'numerical extrema of analytic held segments (velocity roots bisected60 times); not a rigorously rounded upper bound','sampled_peak_V':'evaluated on elapsed grids at most dt apart plus segment endpoints and T','post_T_sampled_peak_V':'same window [T,horizon] in both methods; includes T','terminal_V':'at exactly T=1.25 for both methods, even if T lies between direct-controller updates','command_switches':'adjacent held values differing by more than1e-12; not a performance objective by itself','comparison_scope':'24 pairs, corners and3 rates only; no interior, jitter, error or parameter-grid safety inference'},
 'frozen_model_source_sha256':sources,'hold_sensitivity':hold_checks,'summary':summary,'paired_backup_minus_direct':differences,
 'refinement_check':{'finer_spacing':args.dt/2,'max_post_T_peak_V_change':sensitivity,'interpretation':'sampling sensitivity diagnostic, not an error bound'},'runs':runs}
 (HERE/'experiment-results.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'summary':summary,'refinement_check':out['refinement_check']},indent=2))
if __name__=='__main__':main()
