#!/usr/bin/env python3
"""Summarize new independent replay and compare each decision against frozen05."""
from pathlib import Path
import json,csv,hashlib
H=Path(__file__).resolve().parent;B=H.parent/'builder';OLD=H.parents[1]/'latency-noise-05/grader'
def load(p):return json.loads(p.read_text())
def dump(n,x):(H/n).write_text(json.dumps(x,indent=2)+'\n')
r=load(H/'physical-review.json');o=load(H/'native-oracle.json');pre=load(H/'preflight-review.json');old=load(OLD/'physical-review.json')
assert r['status']=='complete' and r['passed'] and o['all_passed_fixed_limits'] and pre['passed']
rows=r['case_results'];fine=[x for x in rows if x['case_id'].endswith('dt500us')];coarse=[x for x in rows if x['case_id'].endswith('dt1000us')];assert len(fine)==len(coarse)==144
oldmap={x['case_id']:x for x in old['case_results']};assert set(oldmap)=={x['case_id'] for x in rows}
decisions=['endpoint_position_pass','endpoint_velocity_pass','endpoint_acceleration_pass','endpoint_pass','hold_band_pass','internal_tube_sample_pass','required_task_sample_pass']
changes=[];deltas={};worst={};rawfiridentical=True;rawfirhashes=True
for row in rows:
 prior=oldmap[row['case_id']]
 for k in decisions:
  if row['metrics'][k]!=prior['metrics'][k]:changes.append({'case_id':row['case_id'],'metric':k,'old':prior['metrics'][k],'new':row['metrics'][k]})
 for k,v in row['metrics'].items():
  if isinstance(v,(int,float)) and not isinstance(v,bool):
   d=abs(v-prior['metrics'][k])
   if d>deltas.get(k,-1):deltas[k]=d;worst[k]={'case_id':row['case_id'],'old':prior['metrics'][k],'new':v,'abs_difference':d}
 if row['case_id'].split('__')[1] in ['raw','fir']:
  rawfiridentical &= row['metrics']==prior['metrics'];rawfirhashes &= row['row_output_sha256_55_digit']==prior['row_output_sha256_55_digit']
groups={}
for row in fine:
 case,method,rate,w,step=row['case_id'].split('__');groups.setdefault((case,method),[]).append(row)
summary=[];counterexamples=[]
for (case,method),rs in groups.items():
 metrics=[x['metrics'] for x in rs];assert len(rs)==6;hold=case!='persistent_goal'
 ent={'case':case,'method':method,'settings':6,'endpoint_pass_count':sum(x['endpoint_pass'] for x in metrics),'task_pass_count':sum(x['required_task_sample_pass'] for x in metrics),'hold_pass_count':sum(x['hold_band_pass'] is True for x in metrics) if hold else None,
      'hold_peak_min_mm':min(x['hold_peak_m'] for x in metrics)*1000 if hold else None,'hold_peak_max_mm':max(x['hold_peak_m'] for x in metrics)*1000 if hold else None,
      'jerk_energy_min':min(x['actual_jerk_energy_m2_s5'] for x in metrics),'jerk_energy_max':max(x['actual_jerk_energy_m2_s5'] for x in metrics),'command_TV_min':min(x['command_total_variation_m_s2'] for x in metrics),'command_TV_max':max(x['command_total_variation_m_s2'] for x in metrics)}
 if case=='persistent_goal':ent.update(settling_from_commit_min_s=min(x['settling_through_horizon_s']-.22 for x in metrics),settling_from_commit_max_s=max(x['settling_through_horizon_s']-.22 for x in metrics))
 summary.append(ent)
 if hold and not all(x['hold_band_pass'] for x in metrics):
  fail=max(rs,key=lambda x:x['metrics']['hold_peak_m']);counterexamples.append({'case_id':fail['case_id'],'limit_m':.0002,'witness':fail['peak_hold_witness']})
summary.sort(key=lambda x:(x['case'],x['method']));dump('comparison-summary.json',summary);dump('hold-counterexamples.json',counterexamples)
with (H/'comparison-summary.csv').open('w') as f:
 keys=list(dict.fromkeys(k for x in summary for k in x));w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(summary)
dump('comparison-to05.json',{'decision_changes':changes,'max_metric_changes':deltas,'worst_metric_changes':worst,'raw_FIR_all_reviewed_metrics_exactly_equal':rawfiridentical,'raw_FIR_all55digit_row_digests_exactly_equal':rawfirhashes,'old_scope':'05 canonical polynomial result, accepted only within that interpretation. Its native-clock gate remains failed.','new_scope':'06 native-retained-state/binary-origin piecewise polynomial model. Finite native q/v/a checks pass; no bit-identical jerk claim.'})
counts={'parameter_cases':144,'resolutions':2,'trace_count':len(rows),'total_rows':r['total_rows'],'event_rows':r['total_events'],'endpoint_pass_fine':sum(x['metrics']['endpoint_pass'] for x in fine),'task_pass_fine':sum(x['metrics']['required_task_sample_pass'] for x in fine),'endpoint_pass_coarse':sum(x['metrics']['endpoint_pass'] for x in coarse),'task_pass_coarse':sum(x['metrics']['required_task_sample_pass'] for x in coarse),
 'native_plan_count':sum(len(x['plans']) for x in o['streams'].values()),'independent_oracle_absolute_query_count':sum(x['query_count'] for x in o['streams'].values()),'all_saved_native_queries_independently_replayed':load(H/'final-fidelity-review.json')['total_native_queries_independently_replayed'],'primary_local_samples_independently_checked':pre['primary_local_at_time_samples_independently_checked'],'native_pair_pass_count':sum(x['passed_fixed_limits'] for x in o['streams'].values()),'jerk_branch_differences':sum(len(x['jerk_branch_differences']) for x in o['streams'].values()),'task_decision_changes_from05':changes,
 'independent_physical_passed':True,'finite_native_reference_checks_passed':True,'full_bounded_gate_accepted':not changes,'05_failed_native_gate_reclassified':False,'builder_manifest_sha256':r['manifest_before'],'builder_unchanged':r['all_artifacts_unchanged']}
dump('review-summary.json',counts);print(json.dumps(counts,indent=2))
