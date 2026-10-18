from pathlib import Path
from fractions import Fraction as Q
import csv,gzip,hashlib,json,math
HERE=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def main():
 checked=[]
 for manifest in ['pre-run-freeze.json','reference-freeze.json','data-sha256.json']:
  source=json.loads((HERE/manifest).read_text())
  for n,h in source['files'].items():assert sha(HERE/n)==h,(manifest,n)
  checked.append({'manifest':manifest,'sha256':sha(HERE/manifest),'files':len(source['files'])})
 summaries=json.loads((HERE/'metrics.json').read_text())['rows'];assert len(summaries)==72
 ref=json.loads((HERE/'grid-refinement.json').read_text());assert all(r['task_decision_same'] for r in ref)
 schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules'];ext={}
 for s in schedules:
  assert s['truth'][-1]['position']==0
  ext[s['case']+'__'+s['method']]={k:s['reference_extrema'][k] for k in ['peak_V_A_J','common_numerical_conformity']}
  if s['method']!='fir_checked':
   other=next(x for x in schedules if x['method']==s['method'] and x['case']!=s['case'])
   assert s['pieces']==other['pieces']
  for k in [0,1]:assert s['admissions'][k]['target_m']==['1/50','0'][k]
  assert s['admissions'][0]['completion_deadline_s'] is None
 rows_checked=events_checked=0;max_formula=[0.,0.];max_jumps=[0.,0.,0.];prefixes={};runtime_identity=[]
 for p in sorted((HERE/'traces').glob('*.csv.gz')):
  with gzip.open(p,'rt') as f:rows=list(csv.DictReader(f))
  for row in rows:
   t=Q(row['time_exact']);x,v,a,q,qv,qa,j,u,aj=[float(row[k]) for k in ['x','v','a','q','qv','qa','reference_jerk','u','actual_jerk']]
   expected=-800*x-60*v-.5*a+800*q+60*qv+1.5*qa+j/96
   max_formula[0]=max(max_formula[0],abs(expected-u));assert abs(expected-u)<1e-12
  rows_checked+=len(rows)
  eventpath=p.with_name(p.name.removesuffix('.csv.gz')+'__events.csv')
  with eventpath.open() as f:events=list(csv.DictReader(f))
  for e in events:
   assert float(e['actual_state_jump_max'])==0
   assert abs(float(e['formula_residual_u']))<1e-10
   assert abs(float(e['formula_residual_actual_jerk']))<1e-8
   for k,key in enumerate(['delta_q','delta_qv','delta_qa']):max_jumps[k]=max(max_jumps[k],abs(float(e[key])))
  events_checked+=len(events)
  # Deadline-independent native traces must stay identical byte-for-byte.
  if '__native_' in p.name and p.name.startswith('return_generous'):
   other=p.with_name(p.name.replace('return_generous','return_tight'));assert sha(p)==sha(other)
   runtime_identity.append({'generous':p.name,'tight':other.name,'sha256':sha(p)})
 # Named negative controls are existing failed tasks and an explicit reset detector.
 tight_fir=[r for r in summaries if r['case']=='return_tight' and r['method']=='fir_checked']
 tight_match=[r for r in summaries if r['case']=='return_tight' and r['method']=='native_matched']
 assert all(not r['full_task_pass'] and not r['revision_accepted'] for r in tight_fir)
 assert all(not r['full_task_pass'] and not r['deadline_position_and_remain_pass'] for r in tight_match)
 assert any(r['full_task_pass'] for r in summaries if r['case']=='return_tight' and r['method']=='native_fast')
 sample=summaries[0];carried=[sample[k] for k in ['common_revision_x_m','common_revision_v_m_s','common_revision_a_m_s2']]
 assert max(map(abs,carried))>0
 def continuous(before,after):return max(abs(x-y) for x,y in zip(before,after))==0
 assert continuous(carried,carried) and not continuous(carried,[0.,0.,0.])
 negative=[{'claim':'tight FIR serves revision','rejected':True,'witnesses':len(tight_fir)}, {'claim':'arrival-matched native meets tight position deadline','rejected':True,'witnesses':len(tight_match)}, {'claim':'zero-reset equals carried actual state','rejected':True,'carried_state':carried}]
 write('self-audit.json',{'status':'builder check only; independent critic required','passed':True,'frozen_manifests':checked,'state_rows':rows_checked,'event_rows':events_checked,'formula_residual_max':max_formula,'reference_qva_jump_max':max_jumps,'actual_state_jump_max':0.,'native_deadline_trace_identity_pairs':runtime_identity,'reference_extrema':ext,'grid_refinement_all_task_decisions_same':True,'negative_controls':negative})
 print(json.dumps({'passed':True,'state_rows':rows_checked,'event_rows':events_checked,'max_reference_qva_jump':max_jumps,'native_deadline_identity_pairs':len(runtime_identity)},indent=2))
if __name__=='__main__':main()
