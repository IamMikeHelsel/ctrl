"""Saved-data05-to06 metric and tiny-phase jump deltas. No numerical rerun."""
from pathlib import Path
from fractions import Fraction as Q
import csv,json
HERE=Path(__file__).resolve().parent
OLD=HERE.parents[1]/'latency-noise-05/builder'
def key(r):return tuple(r[k] for k in ['method','case','rate','disturbance','sample_step_s'])
old={key(r):r for r in json.loads((OLD/'metrics.json').read_text())['rows']}
new={key(r):r for r in json.loads((HERE/'metrics.json').read_text())['rows']}
fields=['hold_peak_m','internal_error_peak_m','actual_jerk_peak_m_s3','actual_jerk_energy_m2_s5',
        'command_continuous_TV_m_s2','command_jump_TV_m_s2','command_total_variation_m_s2',
        'endpoint_error_m','endpoint_v_m_s','endpoint_a_m_s2','settling_through_horizon_s']
rows=[]
for method,case in sorted({(r['method'],r['case']) for r in new.values()}):
    keys=[k for k,r in new.items() if r['method']==method and r['case']==case and r['sample_step_s']==.0005]
    row={'case':case,'method':method,'parameter_cases':len(keys)}
    for field in fields:
        delta=[new[k][field]-old[k][field] for k in keys if new[k][field] is not None and old[k][field] is not None]
        row[field+'_delta_min']=min(delta) if delta else ''
        row[field+'_delta_max']=max(delta) if delta else ''
    rows.append(row)
with (HERE/'metric-delta-summary.csv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
oldrefs={(r['method'],r['case']):r for r in json.loads((OLD/'reference-schedules.json').read_text())['schedules']}
newrefs={(r['method'],r['case']):r for r in json.loads((HERE/'reference-schedules.json').read_text())['schedules']}
diagnostics=[]
for method,case in sorted(k for k in newrefs if k[0].startswith('ruckig')):
    stages={}
    for label,folder,refs,data in [('05',OLD,oldrefs,old),('06',HERE,newrefs,new)]:
        identity=(method,case,100,0.,.0005);metric=data[identity]
        filename=f'{case}__{method}__r100__w00__dt500us__events.csv'
        events=list(csv.DictReader((folder/'traces'/filename).open()))
        ref=refs[(method,case)]
        tiny=[p for p in ref['pieces'] if 0<Q(p['end_exact'])-Q(p['start_exact'])<=Q(1,10**8)]
        stages[label]={'reference_piece_count':len(ref['pieces']),
                       'executed_positive_pieces_at_most_10ns':tiny,
                       'reference_jerk_jump_count_above_1e_12':sum(abs(float(e['delta_reference_jerk']))>1e-12 for e in events),
                       'reference_jerk_jump_variation_m_s3':sum(abs(float(e['delta_reference_jerk'])) for e in events),
                       'command_continuous_TV_m_s2':metric['command_continuous_TV_m_s2'],
                       'command_jump_TV_m_s2':metric['command_jump_TV_m_s2'],
                       'command_total_variation_m_s2':metric['command_total_variation_m_s2']}
    diagnostics.append({'case':case,'method':method,'representative_rate':100,'representative_disturbance':0.,'sample_step_s':.0005,'stages':stages,
                        'total_TV_delta_m_s2':stages['06']['command_total_variation_m_s2']-stages['05']['command_total_variation_m_s2']})
result={'scope':'Saved-data diagnosis only. All144 cases remain in metrics; this compact structural view uses r100,w0,.5ms. Tiny-phase cutoff is a report label, not a filter or changed execution rule.',
        'mechanism':'At continuous physical state, delta_u=800 delta_q+60 delta_qv+1.5 delta_qa+delta_reference_jerk/96. A very short phase can add finite command variation even when its integrated physical effect is small. No phase is removed in this audit.',
        'rows':diagnostics}
(HERE/'jump-sensitive-delta.json').write_text(json.dumps(result,indent=2)+'\n')
for row in diagnostics:
    if row['method']=='ruckig':
        print(row['case'],'TV delta',row['total_TV_delta_m_s2'],'jerk jumps',*[row['stages'][stage]['reference_jerk_jump_count_above_1e_12'] for stage in ['05','06']],
              'tiny pieces',*[len(row['stages'][stage]['executed_positive_pieces_at_most_10ns']) for stage in ['05','06']])
