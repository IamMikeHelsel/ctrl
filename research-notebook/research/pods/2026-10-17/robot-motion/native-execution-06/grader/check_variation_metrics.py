#!/usr/bin/env python3
from pathlib import Path
import json
H=Path(__file__).resolve().parent;OLD=H.parents[1]/'latency-noise-05/grader'
new=json.loads((H/'physical-review.json').read_text());old=json.loads((OLD/'physical-review.json').read_text());assert new['passed'] and new['status']=='complete'
lookup={r['case_id']:r['metrics'] for r in old['case_results']};exact={r['key']:r for r in json.loads((H/'jump-variation.json').read_text())['rows']};rows=[]
for r in new['case_results']:
 case,method,*_=r['case_id'].split('__')
 if method not in ['ruckig','ruckig_min_08']:continue
 a=lookup[r['case_id']];b=r['metrics'];e=exact[case+'__'+method];jump=b['command_jump_TV_m_s2']-a['command_jump_TV_m_s2'];continuous=b['command_continuous_TV_m_s2']-a['command_continuous_TV_m_s2'];total=b['command_total_variation_m_s2']-a['command_total_variation_m_s2']
 exactdelta=e['new_minus_old_full_jump_TV'];resjump=jump-exactdelta;restotal=total-exactdelta-continuous
 assert abs(resjump)<1e-11 and abs(restotal)<1e-11
 rows.append({'case_id':r['case_id'],'observed_jump_TV_change':jump,'exact_reference_jump_TV_change':exactdelta,'observed_minus_exact_jump_change':resjump,'continuous_TV_change':continuous,'total_TV_change':total,'total_minus_exact_jump_minus_continuous':restotal,'old_exact_jump_TV':e['old05']['full_jump_TV'],'new_exact_jump_TV':e['new06']['full_jump_TV']})
assert len(rows)==144
result={'passed':True,'independently_replayed_metric_rows_checked':len(rows),'units':'m/s^2','max_abs_jump_delta_residual':max(abs(r['observed_minus_exact_jump_change']) for r in rows),'max_abs_total_decomposition_residual':max(abs(r['total_minus_exact_jump_minus_continuous']) for r in rows),'max_abs_continuous_TV_change':max(abs(r['continuous_TV_change']) for r in rows),'max_abs_total_TV_change':max(abs(r['total_TV_change']) for r in rows),'rows':rows}
(H/'variation-metric-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
