from pathlib import Path
from fractions import Fraction as Q
import csv,gzip,hashlib,json,time
from run_comparison import run_case,transition
HERE=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def stem(s,r,w,dt):return f"{s['case']}__{s['method']}__r{r}__w{int(round(w*100)):02d}__dt{int(dt*1000000)}us"
def data_rows(s,r,w,dt):
 with gzip.open(HERE/'traces'/(stem(s,r,w,dt)+'.csv.gz'),'rt') as f:rows=list(csv.DictReader(f))
 for row in rows:
  row['t']=Q(row['time_exact'])
  for k in row:
   if k not in ['time_exact','side','labels','t']:row[k]=float(row[k])
 return rows

def augment(s,r,w,dt):
 rows=data_rows(s,r,w,dt);ready=Q(13,25);issue=Q(1,2);arrival=Q(71,50);horizon=Q(5,2);D=Q(s['deadline_exact'])
 at=lambda t,side='right':next(x for x in rows if x['t']==Q(t) and x['side']==side)
 start=at(0);initial=at(issue);common=at(ready,'left');after=[x for x in rows if x['t']>=D]
 with (HERE/'traces'/(stem(s,r,w,dt)+'__events.csv')).open() as f:jumps=list(csv.DictReader(f))
 match=s['native_duration_match'];accepted=s['revision_accepted'];execution=Q(s['revision_execution_exact']) if accepted else None
 metrics={'initial_progress_m':initial['x']-start['x'],'initial_progress_pass':initial['x']-start['x']>=.001,'revision_accepted':accepted,'revision_execution_s':float(execution) if accepted else None,'wait_after_available_s':float(execution-ready) if accepted else None,'rejected_revision_count':int(not accepted),'planned_reference_arrival_s':float(Q(s['planned_reference_arrival_exact'])),'native_duration_match':match,'reference_deadline_feasible':s['reference_deadline_feasible'],'common_revision_x_m':common['x'],'common_revision_v_m_s':common['v'],'common_revision_a_m_s2':common['a'],'common_revision_q_m':common['q'],'common_revision_qv_m_s':common['qv'],'common_revision_qa_m_s2':common['qa'],'remaining_direct_distance_at_revision_m':abs(common['x']),'deadline_position_and_remain_pass':all(abs(x['x'])<=.0002 for x in after),'deadline_velocity_and_remain_pass':all(abs(x['v'])<=.001 for x in after),'deadline_acceleration_and_remain_pass':all(abs(x['a'])<=.02 for x in after),'tracking_band_sample_pass':all(abs(x['x_minus_q'])<=.0002 for x in rows),'reference_conformity_pass':s['reference_extrema']['common_numerical_conformity'],'reference_exact_extrema':s['reference_extrema']['peak_V_A_J'],'actual_speed_peak_m_s':max(abs(x['v']) for x in rows),'actual_acceleration_peak_m_s2':max(abs(x['a']) for x in rows),'physical_state_jump_max':max(float(x['actual_state_jump_max']) for x in jumps)}
 metrics['full_task_pass']=all(metrics[k] for k in ['initial_progress_pass','revision_accepted','deadline_position_and_remain_pass','deadline_velocity_and_remain_pass','deadline_acceleration_and_remain_pass','tracking_band_sample_pass','reference_conformity_pass'])
 for upper,label in [(arrival,'until_matched_arrival'),(horizon,'until_horizon')]:
  energy=ctv=path=0.
  for a,b in zip(rows,rows[1:]):
   if ready<=a['t']<b['t']<=upper:
    d=float(b['t']-a['t']);energy+=d*(a['actual_jerk']**2+b['actual_jerk']**2)/2;ctv+=d*(abs(a['u_derivative_piecewise'])+abs(b['u_derivative_piecewise']))/2;path+=d*(abs(a['v'])+abs(b['v']))/2
  js=[x for x in jumps if ready<=Q(x['time_exact'])<=upper];part=[x for x in rows if ready<=x['t']<=upper];jtv=sum(abs(float(x['delta_u'])) for x in js)
  metrics.update({f'suffix_{label}_jerk_energy_m2_s5':energy,f'suffix_{label}_command_continuous_TV_m_s2':ctv,f'suffix_{label}_command_jump_TV_m_s2':jtv,f'suffix_{label}_command_total_TV_m_s2':ctv+jtv,f'suffix_{label}_path_length_m':path,f'suffix_{label}_path_minus_direct_distance_m':path-abs(common['x']),f'suffix_{label}_extra_forward_excursion_m':max(0.,max(x['x'] for x in part)-common['x']),f'suffix_{label}_overshoot_beyond_goal_m':max(0.,-min(x['x'] for x in part)),f'suffix_{label}_actual_jerk_peak_m_s3':max(abs(x['actual_jerk']) for x in part),f'suffix_{label}_tracking_error_peak_m':max(abs(x['x_minus_q']) for x in part)})
 return metrics,rows

def main():
 for manifest in ['pre-run-freeze.json','reference-freeze.json']:
  for n,h in json.loads((HERE/manifest).read_text())['files'].items():assert sha(HERE/n)==h,(manifest,n)
 assert json.loads((HERE/'native-pre-run-gate.json').read_text())['passed']
 spec=json.loads((HERE/'inputs.json').read_text());schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules'];summaries=[];events=[];common={};prefixchecks=[];started=time.time()
 for step in map(Q,spec['output_steps']):
  for s in schedules:
   for r in spec['rates']:
    for wq in spec['disturbances']:
     w=float(Q(wq));summary,event=run_case(s,r,w,step);extra,rows=augment(s,r,w,step);summary.update(extra);summaries.append(summary);events.append(event)
     # Compare the physical/reference prefix as serialized values, excluding labels.
     keys=['time_exact','side','q','qv','qa','x','v','a','reference_jerk','u','actual_jerk']
     prefix=[{k:row[k] for k in keys} for row in rows if row['t']<Q(13,25) or (row['t']==Q(13,25) and row['side']=='left')]
     key=(r,wq,str(step));encoded=json.dumps(prefix,sort_keys=True,separators=(',',':')).encode();digest=hashlib.sha256(encoded).hexdigest()
     if key not in common:common[key]=digest
     assert digest==common[key],(s['case'],s['method'],key,'prefix differs')
     prefixchecks.append({'case':s['case'],'method':s['method'],'rate':r,'disturbance':wq,'step':str(step),'prefix_sha256':digest,'prefix_rows':len(prefix),'identical_to_common_prefix':True})
   print(s['case'],s['method'],'dt',float(step),'completed',len(summaries),flush=True)
 write('metrics.json',{'status':'builder numerical evidence; independent review pending','quadrature':'composite trapezoid; command one-sided jumps added exactly as saved','rows':summaries});write('event-states.json',events);write('common-prefix-checks.json',prefixchecks)
 with (HERE/'metrics.csv').open('w',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=list(summaries[0]));writer.writeheader();writer.writerows(summaries)
 data=['metrics.json','metrics.csv','event-states.json','common-prefix-checks.json']+[str(p.relative_to(HERE)) for p in sorted((HERE/'traces').glob('*'))]
 write('data-sha256.json',{'files':{n:sha(HERE/n) for n in data}})
 write('execution-summary.json',{'traces':len(summaries),'state_rows':sum(r['sample_count'] for r in summaries),'prefix_comparisons':len(prefixchecks),'distinct_plant_grid_prefixes':len(common),'elapsed_s':time.time()-started,'transition_cache':str(transition.cache_info())})
 print(json.dumps({'completed':len(summaries),'elapsed_s':time.time()-started},indent=2))
if __name__=='__main__':main()
