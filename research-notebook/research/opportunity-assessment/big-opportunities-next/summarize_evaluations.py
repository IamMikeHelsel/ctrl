from pathlib import Path
import json,hashlib,datetime
B=Path(__file__).resolve().parent
bp=B/'baseline-official-default-local.json';sp=B/'sparse-official-default-local.json'
if not bp.exists() or not sp.exists():
    raise SystemExit('Default-budget pair has not finished; do not report a comparison total.')
b=json.loads(bp.read_text());s=json.loads(sp.read_text())
p=b['evaluation_cohort']['policy'];q=s['evaluation_cohort']['policy']
assert p==q
a=json.loads((B/'official-public-reference-answers.json').read_text())
assert a['spec_sha256']==p['reference_answers']['spec_sha256']
assert [x['n'] for x in a['answers']]==p['inputs']
vals={x['n']:x['value'] for x in a['answers']}
rows=[]
for x,y in zip(b['timing']['scaling'],s['timing']['scaling']):
    assert x['n']==y['n']
    rows.append({'input':x['n'],'dimension':x['n']>>32,'seed':x['n']&((1<<32)-1),
    'exact_output':vals[x['n']], 'baseline_result':x['result'],'sparse_result':y['result'],
    'baseline_kernel_seconds':x.get('median_s'),'sparse_kernel_seconds':y.get('median_s')})
bt=b['replay_report']['computation_total'];st=s['replay_report']['computation_total']
out={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'same_entire_evaluation_policy':True,'cohort':b['evaluation_cohort']['id'],
'metric':'canonical target-declaration kernel-only wall time; one repetition per public case',
'official_instruction_score':False,'baseline_accepted':b['status']=='accepted',
'sparse_accepted':s['status']=='accepted','baseline_complete':b['replay_report']['eligible'],
'sparse_complete':s['replay_report']['eligible'],'baseline_total_seconds':bt,'sparse_total_seconds':st,
'baseline_over_sparse_ratio':bt/st if bt is not None and st is not None else None,
'baseline_cases_passed':sum(x['baseline_result']=='ok' for x in rows),
'sparse_cases_passed':sum(x['sparse_result']=='ok' for x in rows),'cases':rows,
'limitations':['Local Apple M4 Max macOS arm64 host; no official Linux PMU score.','One public-plan repetition per candidate; no uncertainty estimate or current-leaderboard comparison.','Concurrent controls verification about18:19-18:22 UTC, fresh-source build from about18:24 onward, and Erdos compile/replay. Not a controlled benchmark; require quiet repeated runs.','A missing total is not zero and cannot support a full-plan speedup ratio.','Proof targets the fixed generated matrix family for every packed Nat input.']}
(B/'matched-default-comparison.json').write_text(json.dumps(out,indent=2)+'\n')
pair=B/'official-default-local-pair.json'
v=json.loads(pair.read_text())
for n,x in v['results'].items():x['archived_verdict']=f'{n}-official-default-local.json'
pair.write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
