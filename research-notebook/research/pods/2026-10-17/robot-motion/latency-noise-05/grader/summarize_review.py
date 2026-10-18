#!/usr/bin/env python3
from pathlib import Path
import json,csv
H=Path(__file__).resolve().parent;B=H.parent/'builder'
r=json.loads((H/'physical-review.json').read_text());s=json.loads((H/'schedule-review.json').read_text())
assert r['status']=='complete' and s['status']=='complete'
assert r['passed'] and s['canonical_schedule_passed']
rows=r['case_results'];fine=[x for x in rows if x['case_id'].endswith('dt500us')];coarse=[x for x in rows if x['case_id'].endswith('dt1000us')]
assert len(fine)==len(coarse)==144
groups={}
for row in fine:
    case,method,rate,w,step=row['case_id'].split('__');groups.setdefault((case,method),[]).append(row)
summary=[];counterexamples=[]
for (case,method),rs in groups.items():
    assert len(rs)==6
    metrics=[r['metrics'] for r in rs];hold=case!='persistent_goal'
    ent={'case':case,'method':method,'settings':6,'endpoint_pass_count':sum(x['endpoint_pass'] for x in metrics),'task_pass_count':sum(x['required_task_sample_pass'] for x in metrics),
      'hold_pass_count':sum(x['hold_band_pass'] is True for x in metrics) if hold else None,
      'hold_peak_min_mm':min(x['hold_peak_m'] for x in metrics)*1000 if hold else None,'hold_peak_max_mm':max(x['hold_peak_m'] for x in metrics)*1000 if hold else None,
      'internal_tube_pass_count':sum(x['internal_tube_sample_pass'] for x in metrics),'jerk_energy_min':min(x['actual_jerk_energy_m2_s5'] for x in metrics),'jerk_energy_max':max(x['actual_jerk_energy_m2_s5'] for x in metrics),
      'command_TV_min':min(x['command_total_variation_m_s2'] for x in metrics),'command_TV_max':max(x['command_total_variation_m_s2'] for x in metrics)}
    if case=='persistent_goal':
      ent.update(settling_from_commit_min_s=min(x['settling_through_horizon_s']-.22 for x in metrics),settling_from_commit_max_s=max(x['settling_through_horizon_s']-.22 for x in metrics))
    summary.append(ent)
    if hold and not all(x['hold_band_pass'] for x in metrics):
      worst=max(rs,key=lambda x:x['metrics']['hold_peak_m']);counterexamples.append({'case_id':worst['case_id'],'limit_m':.0002,'witness':worst['peak_hold_witness']})
summary.sort(key=lambda x:(x['case'],x['method']))
for name,x in [('comparison-summary.json',summary),('hold-counterexamples.json',counterexamples)]:
 (H/name).write_text(json.dumps(x,indent=2)+'\n')
with (H/'comparison-summary.csv').open('w') as f:
 keys=list(dict.fromkeys(k for x in summary for k in x));out=csv.DictWriter(f,fieldnames=keys);out.writeheader();out.writerows(summary)
counts={'canonical_cases':len(fine),'resolutions':2,'trace_count':len(rows),'total_rows':r['total_rows'],'event_rows':r['total_events'],'endpoint_pass_fine':sum(x['metrics']['endpoint_pass'] for x in fine),
 'task_pass_fine':sum(x['metrics']['required_task_sample_pass'] for x in fine),'endpoint_pass_coarse':sum(x['metrics']['endpoint_pass'] for x in coarse),'task_pass_coarse':sum(x['metrics']['required_task_sample_pass'] for x in coarse),
 'native_plans':sum(x['reproduced_plans'] for x in s['native_exports'].values()),'native_queries':sum(x['query_count'] for x in s['native_clock'].values()),'native_commits':sum(x['commit_count'] for x in s['native_clock'].values()),
 'native_pair_count':len(s['native_clock']),'native_pair_pass_count':sum(x['passed_fixed_state_limits'] for x in s['native_clock'].values()),'native_pair_failures':s['failed_native_streams'],
 'smokes':len(s['smokes']),'tiny_executed_positive_phases':len(s['tiny_executed_phases']),'double_clock_collapsed_positive_phases':sum(x['float_clock_collapses'] for x in s['tiny_executed_phases']),
 'jerk_branch_differences':sum(len(x['jerk_branch_differences']) for x in s['native_clock'].values()),'sampled_counterexample_groups':len(counterexamples),'decision_mismatches':r['decision_mismatches'],
 'canonical_review_passed':True,'native_clock_equivalence_passed':False,'full_gate_accepted':False,'builder_manifest_sha256':r['manifest_before'],'builder_unchanged':r['all_artifacts_unchanged'] and s['all_artifacts_unchanged'],'comparison04_unchanged':s['comparison04_unchanged']}
(H/'review-summary.json').write_text(json.dumps(counts,indent=2)+'\n');print(json.dumps(counts,indent=2))
