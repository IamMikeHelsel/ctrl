#!/usr/bin/env python3
"""Independent 80-digit physical replay: polynomial particular solution plus
3x3 homogeneous matrix exponential. No builder code or simulated states imported.
"""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_left,bisect_right
from functools import lru_cache
from math import factorial
import csv,gzip,hashlib,json,time,sys
import mpmath as mp
mp.mp.dps=80
HERE=Path(__file__).resolve().parent;BUILDER=HERE.parent/'builder-03'
FIELDS=['q','qv','qa','reference_jerk','reference_snap_piecewise','x','v','a','u','actual_jerk','u_derivative_piecewise','truth','x_minus_q','q_minus_truth','x_minus_truth']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def m(q):
    q=Q(q);return mp.mpf(q.numerator)/q.denominator

def ev(cs,t):
    y=mp.mpf(0)
    for c in reversed(cs):y=y*t+c
    return y

@lru_cache(maxsize=None)
def transition(rate,dt):
    if dt==0:return mp.eye(3)
    a=mp.matrix([[0,1,0],[0,0,1],[-800*rate,-60*rate,-mp.mpf(3)*rate/2]])
    return mp.expm(a*m(dt),method='pade')
def mv(M,v):return [sum(M[i,j]*v[j] for j in range(3)) for i in range(3)]

def particular(piece,rate,disturbance):
    # q coefficients encode each frozen binary float exactly before high-precision work.
    q=[Q(piece[k])/factorial(i) for i,k in enumerate(['p','v','a','jerk','snap'])]
    ds=[[q[i]*Q(factorial(i),factorial(i-k)) for i in range(k,5)] for k in range(5)]
    force=[]
    for i in range(5):
        val=800*ds[0][i]+(60*ds[1][i] if i<4 else 0)+(Q(3,2)*ds[2][i] if i<3 else 0)+(ds[3][i]/96 if i<2 else 0)
        force.append(rate*(val+(disturbance if i==0 else 0)))
    p=[Q(0)]*8
    for i in range(4,-1,-1):
        p[i]=(force[i]-Q(3*rate,2)*(i+2)*(i+1)*p[i+2]-60*rate*(i+1)*p[i+1]-(i+3)*(i+2)*(i+1)*p[i+3])/(800*rate)
    for i in range(5):assert 800*rate*p[i]+60*rate*(i+1)*p[i+1]+Q(3*rate,2)*(i+2)*(i+1)*p[i+2]+(i+3)*(i+2)*(i+1)*p[i+3]==force[i]
    pd=[[m(p[i]*Q(factorial(i),factorial(i-k))) for i in range(k,5)] for k in range(3)]
    return [[m(x) for x in d] for d in ds],pd


def reference_extrema(pieces):
    peaks=[mp.mpf(0)]*3
    for p in pieces:
        dur=m(Q(p['end_exact'])-Q(p['start_exact']))
        v,a,j,snap=[m(p[k]) for k in ['v','a','jerk','snap']]
        vc=[mp.mpf(0),dur];ac=[mp.mpf(0),dur]
        if snap:
            disc=j*j-2*snap*a
            if disc>=0:vc.extend([(-j+mp.sqrt(disc))/snap,(-j-mp.sqrt(disc))/snap])
            ac.append(-j/snap)
        elif j:vc.append(-a/j)
        peaks[0]=max([peaks[0]]+[abs(v+a*t+j*t*t/2+snap*t**3/6) for t in vc if 0<=t<=dur])
        peaks[1]=max([peaks[1]]+[abs(a+j*t+snap*t*t/2) for t in ac if 0<=t<=dur])
        peaks[2]=max(peaks[2],abs(j),abs(j+snap*dur))
    return peaks

def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
frozen='abfc9ca6da02e5cbec77b4019e8f356c80d612f65bea3fcb3e7b227ec1cf6d58'
assert sha(BUILDER/'artifact-sha256.json')==frozen
manifest=json.loads((BUILDER/'artifact-sha256.json').read_text())['files']
assert all(sha(BUILDER/n)==v['sha256'] for n,v in manifest.items())
ss=json.loads((BUILDER/'reference-schedules.json').read_text())['schedules']
metrics=json.loads((BUILDER/'metrics.json').read_text())['rows']
assert len(ss)==6 and len(metrics)==72
lookup={(s['case'],s['method']):s for s in ss}
report={'status':'RUNNING','precision':80,'algorithm':'Exact rational polynomial particular solution plus independent 3x3 Pade exponential from zero; no builder Python import','manifest':frozen,'artifact_count':len(manifest),'cases':[], 'row_max_error':{},'event_max_error':{},'metric_max_error':{},'mismatches':[],'rows':0,'events':0}
start=time.monotonic();prefixes={}
for ix,primary in enumerate(metrics):
 s=lookup[primary['case'],primary['method']];rate=primary['rate'];w=Q(str(primary['disturbance']));step=Q(str(primary['sample_step_s']))
 stem=f"{s['case']}__{s['method']}__r{rate}__w{int(w*100):02d}__dt{int(step*1000000)}us"
 pieces=s['pieces'];starts=[Q(p['start_exact']) for p in pieces];ends=[Q(p['end_exact']) for p in pieces]
 assert starts[0]==0 and all(a==b for a,b in zip(ends,starts[1:])) and ends[-1]==Q(5,2)
 models=[particular(p,rate,w) for p in pieces];horizon=ends[-1];deadline=Q(s['deadline_exact'])
 events={Q(e['time_exact']) for e in s['common_events']}|set(starts)|set(ends)
 expected=[]
 for t in sorted(events|{k*step for k in range(int(horizon//step)+1)}):expected.extend([(t,'left'),(t,'right')] if t in events else [(t,'interior')])
 with gzip.open(BUILDER/'traces'/(stem+'.csv.gz'),'rt') as f:saved=list(csv.DictReader(f))
 assert [(Q(r['time_exact']),r['side']) for r in saved]==expected
 assert len(saved)==primary['sample_count']
 state=[mp.mpf(0)]*3;prev_t=Q(0);pi=0;h=[-models[0][1][i][0] for i in range(3)];rows=[];erows=[];errors={k:mp.mpf(0) for k in FIELDS};digest=hashlib.sha256()
 for raw,(t,side) in zip(saved,expected):
  idx=bisect_left(starts,t)-1 if side=='left' and t>0 else bisect_right(starts,t)-1;idx=min(max(idx,0),len(pieces)-1)
  dt=t-prev_t;assert dt>=0 and t<=ends[pi]
  if dt:h=mv(transition(rate,dt),h)
  elapsed=m(t-starts[pi]);state=[ev(models[pi][1][i],elapsed)+h[i] for i in range(3)]
  if idx!=pi:
   assert idx==pi+1 and t==starts[idx]
   pi=idx;elapsed=mp.mpf(0);h=[state[i]-models[idx][1][i][0] for i in range(3)]
  q,qv,qa,j,snap=[ev(d,elapsed) for d in models[idx][0]];x,v,a=state
  u=800*(q-x)+60*(qv-v)+mp.mpf('1.5')*qa-mp.mpf('.5')*a+j/96
  pj=rate*(u+m(w)-a);ud=-800*v-60*a-pj/2+800*qv+60*qa+mp.mpf('1.5')*j+snap/96
  truth=next(m(Q(d['position'])) for d in reversed(s['truth']) if Q(d['time_exact'])<t or (side!='left' and Q(d['time_exact'])==t)) if t!=0 or side!='left' else m(Q(s['truth'][0]['position']))
  vals=dict(zip(FIELDS,[q,qv,qa,j,snap,x,v,a,u,pj,ud,truth,x-q,q-truth,x-truth]));row={'t':t,'side':side,**vals}
  for k,z in vals.items():errors[k]=max(errors[k],abs(z-mp.mpf(raw[k])))
  digest.update((str(t)+'|'+side+'|'+','.join(mp.nstr(vals[k],55) for k in FIELDS)+'\n').encode())
  if rows and dt==0 and side=='right' and t not in [Q(0),horizon]:
   old=rows[-1];dq=[row[k]-old[k] for k in ['q','qv','qa','reference_jerk']];du=u-old['u'];dj=pj-old['actual_jerk'];form=800*dq[0]+60*dq[1]+mp.mpf('1.5')*dq[2]+dq[3]/96
   erows.append({'time_exact':str(t),'delta_q':dq[0],'delta_qv':dq[1],'delta_qa':dq[2],'delta_reference_jerk':dq[3],'delta_u':du,'delta_actual_jerk':dj,'formula_delta_u':form,'formula_residual_u':du-form,'formula_residual_actual_jerk':dj-rate*du,'actual_state_jump_max':max(abs(row[k]-old[k]) for k in ['x','v','a'])})
  rows.append(row);prev_t=t
 def at(t,side='right'):return next(r for r in rows if r['t']==Q(t) and r['side']==side)
 def peak(k,rs=rows):return max(abs(r[k]) for r in rs)
 def integral(k,power=1,lo=Q(0),hi=horizon):return sum((m(b['t']-a['t'])*(abs(a[k])**power+abs(b[k])**power)/2 for a,b in zip(rows,rows[1:]) if lo<=a['t']<b['t']<=hi),mp.mpf(0))
 def jump(k,lo=Q(0),hi=horizon):return sum((abs(r[k]) for r in erows if lo<=Q(r['time_exact'])<=hi),mp.mpf(0))
 def ejpeak(k):return max([mp.mpf(0)]+[abs(r[k]) for r in erows])
 ep=at(deadline);c=at(Q(13,25),'left');initial=at(Q(1,2));after=[r for r in rows if r['t']>=deadline]
 bands=[('x',mp.mpf('.0002')),('v',mp.mpf('.001')),('a',mp.mpf('.02'))]
 tests=[abs(ep[k])<=lim for k,lim in bands];remains=[all(abs(r[k])<=lim for r in after) for k,lim in bands]
 good=[all(abs(r[k])<=lim for k,lim in bands) for r in rows];lastbad=max((i for i,b in enumerate(good) if not b),default=-1);settling=None if lastbad==len(rows)-1 else float(rows[lastbad+1]['t'])
 e=integral('actual_jerk',2);tv=integral('u_derivative_piecewise');jt=jump('delta_u');refpeaks=reference_extrema(pieces);conform=all(z<=mp.mpf(l)+mp.mpf('1e-10') for z,l in zip(refpeaks,['.1','.5','7.5']))
 measured={'endpoint_error_m':ep['x_minus_truth'],'endpoint_v_m_s':ep['v'],'endpoint_a_m_s2':ep['a'],'endpoint_position_pass':tests[0],'endpoint_velocity_pass':tests[1],'endpoint_acceleration_pass':tests[2],'endpoint_pass':all(tests),'hold_peak_m':peak('x'),'hold_band_pass':'','internal_error_peak_m':peak('x_minus_q'),'internal_tube_sample_pass':peak('x_minus_q')<=mp.mpf('.0002'),'true_error_peak_m':peak('x_minus_truth'),'shaping_error_peak_m':peak('q_minus_truth'),'settling_through_horizon_s':settling,'actual_jerk_peak_m_s3':peak('actual_jerk'),'actual_jerk_energy_m2_s5':e,'actual_jerk_rms_m_s3':mp.sqrt(e/m(horizon)),'command_peak_m_s2':peak('u'),'command_continuous_TV_m_s2':tv,'command_jump_TV_m_s2':jt,'command_total_variation_m_s2':tv+jt,'largest_command_jump_m_s2':ejpeak('delta_u'),'largest_actual_jerk_jump_m_s3':ejpeak('delta_actual_jerk'),'reference_velocity_peak_m_s':peak('qv'),'reference_acceleration_peak_m_s2':peak('qa'),'reference_jerk_piecewise_peak_m_s3':peak('reference_jerk'),'reference_position_jump_peak_m':ejpeak('delta_q'),'reference_velocity_jump_peak_m_s':ejpeak('delta_qv'),'reference_acceleration_jump_peak_m_s2':ejpeak('delta_qa'),'actual_state_jump_max':ejpeak('actual_state_jump_max'),'required_task_sample_pass':all(tests),'command_jump_formula_max_residual':ejpeak('formula_residual_u'),'actual_jerk_jump_formula_max_residual':ejpeak('formula_residual_actual_jerk'),'initial_progress_m':initial['x'],'initial_progress_pass':initial['x']>=mp.mpf('.001'),'common_revision_x_m':c['x'],'common_revision_v_m_s':c['v'],'common_revision_a_m_s2':c['a'],'common_revision_q_m':c['q'],'common_revision_qv_m_s':c['qv'],'common_revision_qa_m_s2':c['qa'],'remaining_direct_distance_at_revision_m':abs(c['x']),'deadline_position_and_remain_pass':remains[0],'deadline_velocity_and_remain_pass':remains[1],'deadline_acceleration_and_remain_pass':remains[2],'tracking_band_sample_pass':peak('x_minus_q')<=mp.mpf('.0002'),'reference_conformity_pass':conform,'actual_speed_peak_m_s':peak('v'),'actual_acceleration_peak_m_s2':peak('a'),'physical_state_jump_max':ejpeak('actual_state_jump_max')}
 accepted=all(a['outcome']=='accepted' for a in s['admissions']);measured['revision_accepted']=accepted;measured['rejected_revision_count']=int(not accepted)
 measured['full_task_pass']=bool(measured['initial_progress_pass'] and accepted and all(remains) and measured['tracking_band_sample_pass'] and conform)
 for upper,label in [(Q(71,50),'until_matched_arrival'),(horizon,'until_horizon')]:
  lo=Q(13,25);rs=[r for r in rows if lo<=r['t']<=upper];energy=integral('actual_jerk',2,lo,upper);ctv=integral('u_derivative_piecewise',1,lo,upper);jtv=jump('delta_u',lo,upper);path=integral('v',1,lo,upper)
  vals={'jerk_energy_m2_s5':energy,'command_continuous_TV_m_s2':ctv,'command_jump_TV_m_s2':jtv,'command_total_TV_m_s2':ctv+jtv,'path_length_m':path,'path_minus_direct_distance_m':path-abs(c['x']),'extra_forward_excursion_m':max(mp.mpf(0),max(r['x'] for r in rs)-c['x']),'overshoot_beyond_goal_m':max(mp.mpf(0),-min(r['x'] for r in rs)),'actual_jerk_peak_m_s3':peak('actual_jerk',rs),'tracking_error_peak_m':peak('x_minus_q',rs)}
  measured.update({'suffix_'+label+'_'+k:v for k,v in vals.items()})
 diffs={}
 for k,z in measured.items():
  p=primary[k]
  if isinstance(z,bool) or z is None or z=='':
   if z!=p:report['mismatches'].append([stem,k,p,z])
  else:
   d=abs(float(z)-p);diffs[k]=d;report['metric_max_error'][k]=max(d,report['metric_max_error'].get(k,0))
 with (BUILDER/'traces'/(stem+'__events.csv')).open() as f:savedevents=list(csv.DictReader(f))
 assert len(erows)==len(savedevents)
 for a,b in zip(erows,savedevents):
  assert a['time_exact']==b['time_exact']
  for k,z in a.items():
   if k!='time_exact':report['event_max_error'][k]=max(float(abs(z-mp.mpf(b[k]))),report['event_max_error'].get(k,0))
 prefix=[r for r in rows if r['t']<Q(13,25) or (r['t']==Q(13,25) and r['side']=='left')]
 pdigest=hashlib.sha256('\n'.join(str(r['t'])+'|'+r['side']+'|'+','.join(mp.nstr(r[k],55) for k in FIELDS) for r in prefix).encode()).hexdigest();pk=(rate,str(w),str(step))
 if pk in prefixes:assert prefixes[pk]==pdigest,(stem,'independent prefix mismatch')
 else:prefixes[pk]=pdigest
 for k,z in errors.items():report['row_max_error'][k]=max(float(z),report['row_max_error'].get(k,0))
 report['cases'].append({'case_id':stem,'row_count':len(rows),'event_count':len(erows),'output_sha256_55_digits':digest.hexdigest(),'prefix_sha256_55_digits':pdigest,'metric_differences':diffs,'metrics':{k:float(z) if isinstance(z,mp.mpf) else z for k,z in measured.items()},'reference_critical_peaks':[float(z) for z in refpeaks]})
 report['rows']+=len(rows);report['events']+=len(erows);report['elapsed_seconds']=time.monotonic()-start;dump(HERE/'physical-review.json',report)
 print(ix+1,stem,'max x error',float(errors['x']),'full task',measured['full_task_pass'],flush=True)
assert report['rows']==271884 and report['events']==1356
report['all_frozen_files_unchanged']=all(sha(BUILDER/n)==v['sha256'] for n,v in manifest.items()) and sha(BUILDER/'artifact-sha256.json')==frozen
report['passed']=not report['mismatches'] and report['all_frozen_files_unchanged'] and max(report['row_max_error'].values())<1e-7 and max(report['metric_max_error'].values())<1e-7
report['distinct_prefixes']=len(prefixes);report['status']='COMPLETE';dump(HERE/'physical-review.json',report)
print(json.dumps({k:v for k,v in report.items() if k not in ['cases','metric_max_error','event_max_error']}),flush=True)
