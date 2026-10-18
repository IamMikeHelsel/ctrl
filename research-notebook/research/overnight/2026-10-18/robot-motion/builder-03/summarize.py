from pathlib import Path
import json,csv,hashlib
HERE=Path(__file__).resolve().parent
rows=json.loads((HERE/'metrics.json').read_text())['rows'];fine=[r for r in rows if r['sample_step_s']==.0005];table=[]
fields=['internal_error_peak_m','actual_jerk_peak_m_s3','actual_speed_peak_m_s','actual_acceleration_peak_m_s2','command_peak_m_s2','suffix_until_horizon_jerk_energy_m2_s5','suffix_until_horizon_command_total_TV_m_s2','suffix_until_horizon_extra_forward_excursion_m','suffix_until_horizon_overshoot_beyond_goal_m','suffix_until_horizon_path_length_m','suffix_until_horizon_path_minus_direct_distance_m','suffix_until_matched_arrival_jerk_energy_m2_s5','settling_through_horizon_s']
for case in ['return_generous','return_tight']:
 for method in ['fir_checked','native_fast','native_matched']:
  rs=[r for r in fine if r['case']==case and r['method']==method]
  out={'case':case,'method':method,'n':len(rs),'task_passes':sum(r['full_task_pass'] for r in rs),'requests_accepted':sum(r['revision_accepted'] for r in rs),'tracking_passes':sum(r['tracking_band_sample_pass'] for r in rs),'position_passes':sum(r['deadline_position_and_remain_pass'] for r in rs),'velocity_passes':sum(r['deadline_velocity_and_remain_pass'] for r in rs),'acceleration_passes':sum(r['deadline_acceleration_and_remain_pass'] for r in rs),'reference_conformity_passes':sum(r['reference_conformity_pass'] for r in rs),'wait_s':rs[0]['wait_after_available_s'],'reference_arrival_s':rs[0]['planned_reference_arrival_s'],'duration_match':rs[0]['native_duration_match']}
  for key in fields:
   values=[r[key] for r in rs if r[key] is not None];out[key+'_min']=min(values) if values else None;out[key+'_max']=max(values) if values else None
  table.append(out)
ref=[]
for a in fine:
 b=next(r for r in rows if all(r[k]==a[k] for k in ['case','method','rate','disturbance']) and r['sample_step_s']==.001)
 ref.append({'case':a['case'],'method':a['method'],'rate':a['rate'],'disturbance':a['disturbance'],'task_decision_same':a['full_task_pass']==b['full_task_pass'],'absolute_change':{k:abs(a[k]-b[k]) if a[k] is not None and b[k] is not None else None for k in fields}})
(HERE/'comparison-summary.json').write_text(json.dumps({'scope':'fine-grid ranges across six constant plant cases, not a robust theorem','rows':table},indent=2)+'\n');(HERE/'grid-refinement.json').write_text(json.dumps(ref,indent=2)+'\n')
with (HERE/'comparison-summary.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=list(table[0]));w.writeheader();w.writerows(table)
print(json.dumps(table,indent=2))
