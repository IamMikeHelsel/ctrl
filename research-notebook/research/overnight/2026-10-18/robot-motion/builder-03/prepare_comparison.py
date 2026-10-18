from pathlib import Path
from fractions import Fraction as Q
from math import factorial
from copy import deepcopy
from bisect import bisect_right
import hashlib,json,subprocess
from make_references import fir,state_at,ordinary_piece
from prepare import schedule,reference_extrema
from ruckig_checks import validate,reconstruct
HERE=Path(__file__).resolve().parent

def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 frozen=json.loads((HERE/'pre-run-freeze.json').read_text())
 for n,h in frozen['files'].items():assert sha(HERE/n)==h,n
 spec=json.loads((HERE/'inputs.json').read_text());ready=Q(spec['revision_ready']);end=Q(spec['horizon']);h=Q(spec['fir_h']);old=[(Q(spec['first_ready']),Q(spec['first_goal']))]
 full=fir(old,h,end);prefix=[]
 for p in full:
  if Q(p['start_exact'])>=ready:break
  p=deepcopy(p);p['end_exact']=str(min(ready,Q(p['end_exact'])));p['end']=float(Q(p['end_exact']));prefix.append(p)
 base=prefix[-1];dt=ready-Q(base['start_exact']);ds=list(map(Q,base['rational_derivatives_at_start']));state=[sum(ds[k+i]*dt**i/factorial(i) for i in range(5-k)) for k in range(3)]
 write('common-reference-state.json',{'revision_ready_exact':str(ready),'rational_qva':list(map(str,state)),'binary_qva':list(map(float,state)),'binary_qva_hex':[float(x).hex() for x in state],'prefix':prefix})
 native={};nativechecks={};folder=HERE/'native-plans';folder.mkdir(exist_ok=True)
 for method,minimum in [('native_fast',0.),('native_matched',float(Q(spec['matched_minimum_duration'])))]:
  queries=sorted(set([float(Q(k,2000)) for k in range(int((end-ready)*2000)+1)]+[float(end-ready)]))
  text=' '.join(f'{float(x):.17g}' for x in [*state,Q(spec['revision_goal'])])+'\n'+str(len(queries))+'\n'+'\n'.join(f'{t:.17g}' for t in queries)+'\n'
  (folder/(method+'-input.txt')).write_text(text)
  run=subprocess.run([str(HERE/'.cache/native_suffix'),str(minimum)],input=text,text=True,capture_output=True)
  (folder/(method+'-stderr.txt')).write_text(run.stderr);(folder/(method+'-export.json')).write_text(run.stdout);run.check_returncode();record=json.loads(run.stdout)
  if not record['accepted']:native[method]={'accepted':False,'pieces':full,'failure':record};continue
  plan=record['plan'];plan['input']={'state':list(map(float,state)),'target':0.,'minimum_duration':minimum,'queries':queries};check=validate(plan)
  run2=subprocess.run([str(HERE/'.cache/native_queries'),str(minimum)],input=text,text=True,capture_output=True)
  (folder/(method+'-queries-stderr.txt')).write_text(run2.stderr);(folder/(method+'-queries.json')).write_text(run2.stdout);run2.check_returncode();replay=json.loads(run2.stdout)
  maxima=[0.,0.,0.];jerkmax=0.;mismatch=0
  for row in replay['queries']:
   got=reconstruct(plan,row['t']);actual=[row[k] for k in ['p','v','a']];maxima=[max(a,abs(x-y)) for a,x,y in zip(maxima,got,actual)]
   phase=plan['tail'] if row['t']>=plan['duration'] else [p for p in plan['phases'] if p['duration']>0 and p['start']<=row['t']][-1]
   jerkmax=max(jerkmax,abs(phase['jerk']-row['jerk']));mismatch+=phase['jerk']!=row['jerk']
  assert all(a<=b for a,b in zip(maxima,spec['native_replay_qva_allowances'])),maxima
  assert jerkmax<=spec['native_jerk_allowance'],jerkmax
  pieces=deepcopy(prefix)
  for phase in plan['phases']:
   if phase['duration']<=0:continue
   start=ready+Q(phase['start']);finish=min(end,ready+Q(phase['end']))
   if finish>start:pieces.append(ordinary_piece(start,finish,[phase[k] for k in ['p','v','a','jerk']]+[0.],method+'_'+phase['kind']+'_'+str(phase['index'])))
  tail=plan['tail'];start=ready+Q(tail['start'])
  if start<end:pieces.append(ordinary_piece(start,end,[tail[k] for k in ['p','v','a','jerk']]+[0.],method+'_tail'))
  arrival=ready+Q(plan['duration']);match=abs(plan['duration']-float(Q(spec['matched_minimum_duration'])))<=spec['native_duration_match_allowance_s'] if method=='native_matched' else None
  native[method]={'accepted':True,'pieces':pieces,'plan':plan,'reference_arrival_exact':str(arrival),'duration_match':match}
  nativechecks[method]={'passed':True,'profile_check':check,'query_count':len(replay['queries']),'query_max_abs_qva':maxima,'query_max_abs_jerk':jerkmax,'jerk_branch_mismatches':mismatch,'duration':plan['duration'],'duration_match':match}
 write('native-pre-run-gate.json',{'passed':all(v['passed'] for v in nativechecks.values()),'cases':nativechecks})
 write('native-suffix-records.json',native)
 schedules=[];transcripts=[]
 shared={Q(x) for x in ['0','1/5','11/50','1/2','13/25','3/5','31/50','4/5','1','51/50','33/25','71/50','13/10','17/10','5/2']}
 for caseid,D in spec['deadlines'].items():
  task={'id':caseid,'end_s':str(end),'deadline_s':D,'revision_issue_s':spec['revision_issue'],'revision_ready_s':str(ready),'truth':[{'time_s':'0','position_m':'0'},{'time_s':spec['first_issue'],'position_m':spec['first_goal']},{'time_s':spec['revision_issue'],'position_m':'0'}], 'packets':[{'sequence':1,'observed_s':spec['first_issue'],'ready_s':spec['first_ready'],'target_m':spec['first_goal'],'completion_deadline_s':None},{'sequence':2,'observed_s':spec['revision_issue'],'ready_s':str(ready),'target_m':'0','completion_deadline_s':D}]}
  events,value,outcomes=schedule(task,'fir_checked')
  for method in spec['methods']:
   if method=='fir_checked':
    pieces=fir(events,h,end);admissions=deepcopy(outcomes);arrival=max(t for t,d in events)+4*h;match=None;accepted=outcomes[-1]['outcome']=='accepted';execution=outcomes[-1]['actual_selected_execution_s']
   else:
    n=native[method];accepted=n['accepted'];pieces=deepcopy(n['pieces']);arrival=Q(n['reference_arrival_exact']) if accepted else max(t for t,d in old)+4*h;match=n.get('duration_match');execution=str(ready) if accepted else None
    admissions=[deepcopy(outcomes[0]),{**task['packets'][1],'admission_s':str(ready),'commit_s':str(ready),'execution_s':str(ready),'actual_selected_execution_s':execution,'outcome':'accepted' if accepted else 'native_rejected','native_duration_match':match,'native_reference_deadline_feasible':accepted and arrival<=Q(D)}]
   assert Q(pieces[0]['start_exact'])==0 and Q(pieces[-1]['end_exact'])==end
   for a,b in zip(pieces,pieces[1:]):assert Q(a['end_exact'])==Q(b['start_exact']),(method,a,b)
   common={t:['shared_scoring_probe'] for t in shared}
   for t in [ready,arrival]:common.setdefault(t,[]).append('revision_availability' if t==ready else 'planned_reference_arrival')
   # Same event partition before and at revision availability is required for bitwise carried-state equality.
   bounds=reference_extrema(pieces)
   row={'case':caseid,'method':method,'hold_required':False,'horizon_exact':str(end),'deadline_exact':D,'truth':[{'time_exact':r['time_s'],'position':float(Q(r['position_m']))} for r in task['truth']],'common_events':[{'time_exact':str(t),'labels':labs} for t,labs in sorted(common.items())],'admissions':admissions,'final_accepted_goal':0. if accepted else float(Q(spec['first_goal'])),'pieces':pieces,'reference_extrema':bounds,'task_spec':task,'revision_accepted':accepted,'revision_execution_exact':execution,'planned_reference_arrival_exact':str(arrival),'native_duration_match':match,'reference_deadline_feasible':accepted and arrival<=Q(D)}
   schedules.append(row);transcripts.append({'case':caseid,'method':method,'admissions':admissions,'FIR_events':[[str(t),str(d)] for t,d in events] if method=='fir_checked' else None})
 write('reference-schedules.json',{'schedules':schedules});write('admission-transcripts.json',transcripts)
 generated=['common-reference-state.json','native-pre-run-gate.json','native-suffix-records.json','reference-schedules.json','admission-transcripts.json']+[str(p.relative_to(HERE)) for p in sorted(folder.glob('*'))]
 write('reference-freeze.json',{'files':{n:sha(HERE/n) for n in generated}})
 print(json.dumps({'schedules':len(schedules),'native_checks':nativechecks,'common_qva':list(map(str,state))},indent=2))
if __name__=='__main__':main()
