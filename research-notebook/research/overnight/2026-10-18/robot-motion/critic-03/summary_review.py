"""Recompute comparison ranges and paired tradeoffs from independent replay."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent;B=HERE.parent/'builder-03'
replay=json.loads((HERE/'physical-review.json').read_text());assert replay['passed']
primary=json.loads((B/'metrics.json').read_text())['rows'];saved=json.loads((B/'comparison-summary.json').read_text())['rows']
rs={r['case_id']:r['metrics'] for r in replay['cases']}
groups={};pairs={};verified=0;maxdiff=0.
countmap={'task_passes':'full_task_pass','requests_accepted':'revision_accepted','tracking_passes':'tracking_band_sample_pass','position_passes':'deadline_position_and_remain_pass','velocity_passes':'deadline_velocity_and_remain_pass','acceleration_passes':'deadline_acceleration_and_remain_pass','reference_conformity_passes':'reference_conformity_pass'}
for row in primary:
 if row['sample_step_s']!=.0005:continue
 key=(row['case'],row['method']);caseid=f"{row['case']}__{row['method']}__r{row['rate']}__w{int(row['disturbance']*100):02d}__dt500us";v=rs[caseid]
 groups.setdefault(key,[]).append(v)
 if row['case']=='return_generous':pairs.setdefault((row['rate'],row['disturbance']),{})[row['method']]=v
for s in saved:
 g=groups[s['case'],s['method']];assert len(g)==s['n']==6
 for k,metric in countmap.items():assert s[k]==sum(r[metric] for r in g);verified+=1
 for k,v in s.items():
  if k.endswith(('_min','_max')):
   name,which=k.rsplit('_',1);vals=[r[name] for r in g]
   result=(min(vals) if which=='min' else max(vals)) if all(x is not None for x in vals) else None
   if result is None:assert v is None
   else:maxdiff=max(maxdiff,abs(result-v));assert abs(result-v)<1e-7,(k,result,v)
   verified+=1
ratios={}
for method in ['native_fast','native_matched']:
 ratios[method]={}
 for label,metric in [('jerk_squared','suffix_until_horizon_jerk_energy_m2_s5'),('forward_excursion','suffix_until_horizon_extra_forward_excursion_m'),('path_length','suffix_until_horizon_path_length_m')]:
  vals=[v['fir_checked'][metric]/v[method][metric] for v in pairs.values()];ratios[method][label]=[min(vals),max(vals)]
counts=[{'case':c,'method':m,'passes':sum(r['full_task_pass'] for r in g),'n':len(g),'accepted':sum(r['revision_accepted'] for r in g)} for (c,m),g in groups.items()]
out={'status':'PASS','summary_fields_checked':verified,'max_range_difference':maxdiff,'paired_FIR_to_native_ratios':ratios,'task_counts':counts,'metrics_scope':'Two fixed suffix horizons: [0.52,1.42] and [0.52,2.5] s. Trapezoidal actual jerk squared and path, command derivative variation plus exact saved one-sided jumps. Peaks are sampled, including event sides. No all-time physical peak or optimality claim.','units':{'squared_jerk_integral':'m^2/s^5, not physical energy','command_total_variation':'m/s^2','extra_forward_excursion':'m beyond physical x at revision, not overshoot past the final goal'},'fairness_boundary':'Identical actual/reference prefix and modeled plant. Different suffix geometry and reference jerk shape. Native minimum_duration is not a minimum squared-jerk solver. No path cap or actuator effort minimization is matched.'}
(HERE/'summary-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
