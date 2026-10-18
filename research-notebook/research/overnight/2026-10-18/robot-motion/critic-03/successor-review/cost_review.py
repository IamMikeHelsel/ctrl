from pathlib import Path
from statistics import median
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out={'status':'PASS','scope':'Read-only protocol, source binding, all timing rows and arithmetic. No new timing run, native production or worst-case execution claim.','studies':{}}
for key,folder in [('new','successor-check-01'),('old','checker-cost-02')]:
 p=ROOT/folder;data=json.loads((p/'results.json').read_text());rows=data['rows'];assert len(rows)==18
 assert data['inputs_unchanged'] and data['execution']=='Lean --run; shared active host; internal result print included'
 assert all(sha(ROOT/n)==h for n,h in data['binding'].items())
 stats=[]
 for n in [1,2,4,8,16,32]:
  r=[x for x in rows if x['events']==n];assert sorted(x['repetition'] for x in r)==[1,2,3]
  for x in r:
   assert x['status']=='completed' and x['exit_code']==0 and x['accepted']
   assert re.search(r'accepted=true\n',x['output']) and int(re.search(r'nanoseconds=(\d+)',x['output'])[1])==x['checker_nanoseconds_including_print']
   assert x['process_seconds']>x['checker_nanoseconds_including_print']/1e9
  vals=[x['checker_nanoseconds_including_print']/1e6 for x in r]
  stats.append({'n':n,'median_ms':median(vals),'min_ms':min(vals),'max_ms':max(vals),'all_ms':vals})
 out['studies'][key]={'results_sha256':sha(p/'results.json'),'benchmark_sha256':sha(p/'Benchmark.lean'),'started_utc':data['started_utc'],'finished_utc':data['finished_utc'],'rows':stats,'all_18_accepted':True}
a=(ROOT/'successor-check-01/Benchmark.lean').read_text();b=(ROOT/'checker-cost-02/Benchmark.lean').read_text()
for text in [a,b]:
 for expression in ['(List.range n).map','(i : Rat) / 100','if i % 2 = 0 then (1 : Rat) / 1000 else -(1 : Rat) / 1000','(1/5) (1/2) 0 es','IO.monoNanosNow','IO.println s!"accepted={accepted}"']:
  assert expression in text,expression
out['same_fixed_input_and_internal_timer_convention']=True
out['observed_old_to_new_32_median_ratio']=out['studies']['old']['rows'][-1]['median_ms']/out['studies']['new']['rows'][-1]['median_ms']
out['interpretation']='About 102.53-fold ratio of recorded medians in different shared-host runs, not a controlled hardware speedup or a real-time bound. One-event new median is slower. No pruning combination was timed.'
(HERE/'cost-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
