"""Compare fixed144 results with05 and sampling refinement; no physical runs."""
from pathlib import Path
from fractions import Fraction as Q
import csv,hashlib,json,platform,sys
import numpy,scipy
HERE=Path(__file__).resolve().parent
OLD=HERE.parents[1]/'latency-noise-05/builder'
METHODS=['raw','ruckig','ruckig_min_08','fir']
CASES=['hold_jitter','persistent_goal','sign_60ms','irregular_alternation','seeded_random','biased_alternation']
def read(name):return json.loads((HERE/name).read_text())
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def key(r):return tuple(r[k] for k in ['method','case','rate','disturbance'])
def fullkey(r):return key(r)+(r['sample_step_s'],)
def main():
    rows=read('metrics.json')['rows'];old=json.loads((OLD/'metrics.json').read_text())['rows']
    oldmap={fullkey(r):r for r in old};newmap={fullkey(r):r for r in rows}
    assert set(oldmap)==set(newmap) and len(rows)==288
    coarse={key(r):r for r in rows if r['sample_step_s']==.001}
    fine={key(r):r for r in rows if r['sample_step_s']==.0005}
    expected={(m,c,r,w) for m in METHODS for c in CASES for r in [80,100,120] for w in [0.,.01]}
    assert set(coarse)==set(fine)==expected
    decisions=['endpoint_position_pass','endpoint_velocity_pass','endpoint_acceleration_pass','endpoint_pass',
               'hold_band_pass','internal_tube_sample_pass','required_task_sample_pass']
    fields=['hold_peak_m','internal_error_peak_m','true_error_peak_m','shaping_error_peak_m',
            'actual_jerk_peak_m_s3','actual_jerk_energy_m2_s5','command_total_variation_m_s2',
            'largest_command_jump_m_s2','largest_actual_jerk_jump_m_s3','endpoint_error_m',
            'endpoint_v_m_s','endpoint_a_m_s2','settling_through_horizon_s']
    changes=[];numerical=[];raw_fir_identical=0
    for identity,row in newmap.items():
        previous=oldmap[identity]
        diff={name:{'old05':previous[name],'new06':row[name]} for name in decisions if previous[name]!=row[name]}
        if diff:changes.append({'case':identity,'decisions':diff})
        numerical.append({'case':identity,'absolute_changes':{name:abs(row[name]-previous[name]) for name in fields if row[name] is not None and previous[name] is not None}})
        if row['method'] in ['raw','fir']:
            assert row==previous,(identity,'raw/FIR changed');raw_fir_identical+=1
    write('decision-comparison-05.json',{'status':'finite canonical05 versus native-state polynomial06 comparison; does not retroactively accept05',
          'compared_rows':288,'changed_decision_rows':changes,'raw_fir_rows_identical':raw_fir_identical,
          'maximum_absolute_metric_changes':{name:max(r['absolute_changes'].get(name,0) for r in numerical) for name in fields},'rows':numerical})
    refinement=[];refinement_decisions=[]
    for identity,a in coarse.items():
        b=fine[identity]
        for name in decisions:
            if a[name]!=b[name]:refinement_decisions.append({'case':identity,'field':name,'coarse':a[name],'fine':b[name]})
        refinement.append({'case':identity,'changes':{name:{'coarse':a[name],'fine':b[name],'absolute_change':abs(a[name]-b[name]),'relative_change_to_fine':abs(a[name]-b[name])/max(abs(b[name]),1e-30)} for name in fields if a[name] is not None and b[name] is not None}})
    states={x['case_id']:x['states'] for x in read('event-states.json')};state_error=[0.,0.,0.]
    for name,values in states.items():
        if not name.endswith('dt1000us'):continue
        other=states[name[:-8]+'dt500us'];assert len(values)==len(other)
        for a,b in zip(values,other):
            assert a['time_exact']==b['time_exact']
            state_error=[max(v,abs(a[k]-b[k])) for v,k in zip(state_error,['x','v','a'])]
    write('refinement.json',{'status':'same-builder sampling refinement, not independent review','decision_changes':refinement_decisions,
          'maximum_event_state_changes':state_error,'maximum_metric_changes':{name:{'max_absolute_change':max(x['changes'][name]['absolute_change'] for x in refinement if name in x['changes']),
          'max_relative_change_to_fine':max(x['changes'][name]['relative_change_to_fine'] for x in refinement if name in x['changes'])} for name in fields},'cases':refinement})
    overview=[]
    for case in CASES:
        for method in METHODS:
            subset=[r for r in fine.values() if r['case']==case and r['method']==method]
            ranges={name:[min(r[name] for r in subset if r[name] is not None),max(r[name] for r in subset if r[name] is not None)] if any(r[name] is not None for r in subset) else None for name in fields}
            overview.append({'case':case,'method':method,'endpoint_passes':sum(r['endpoint_pass'] for r in subset),
                             'task_passes':sum(r['required_task_sample_pass'] for r in subset),
                             'hold_passes':sum(r['hold_band_pass'] is True for r in subset) if case!='persistent_goal' else None,'ranges':ranges})
    summary={'status':'builder06 complete; independent physical review pending; failed05 remains failed',
             'parameter_cases':144,'metric_rows':288,'endpoint_passes':sum(r['endpoint_pass'] for r in fine.values()),
             'task_passes':sum(r['required_task_sample_pass'] for r in fine.values()),
             'changed_decision_rows_from05':len(changes),'raw_fir_rows_identical_to05':raw_fir_identical,
             'refinement_decision_changes':len(refinement_decisions),'actual_state_jump_max':max(r['actual_state_jump_max'] for r in rows),'overview':overview}
    write('audit-summary.json',summary)
    table=[]
    for row in overview:
        values={k:row[k] for k in ['case','method','endpoint_passes','task_passes','hold_passes']}
        for name,span in row['ranges'].items():values[name+'_min']=span[0] if span else '';values[name+'_max']=span[1] if span else ''
        table.append(values)
    with (HERE/'comparison-table.csv').open('w',newline='') as file:
        writer=csv.DictWriter(file,fieldnames=list(table[0]));writer.writeheader();writer.writerows(table)
    exports=read('ruckig-primary-exports.json');latency=[]
    for method in METHODS:
        subset=[r for r in fine.values() if r['case']=='persistent_goal' and r['method']==method]
        duration=exports['persistent_goal__'+method][0]['plan']['duration'] if method.startswith('ruckig') else (.8 if method=='fir' else 0.)
        origin=Q(exports['persistent_goal__'+method][0]['native_commit_exact']) if method.startswith('ruckig') else Q(11,50)
        latency.append({'method':method,'execution_origin_exact':str(origin),'reference_duration_s':duration,
                        'reference_endpoint_absolute_s':float(origin)+duration,
                        'actual_settling_absolute_range_s':[min(r['settling_through_horizon_s'] for r in subset),max(r['settling_through_horizon_s'] for r in subset)],
                        'actual_settling_after_commit_range_s':[min(r['settling_through_horizon_s']-float(origin) for r in subset),max(r['settling_through_horizon_s']-float(origin) for r in subset)]})
    write('isolated-step-latency.json',{'status':'sampled settling through fixed horizon; no equal-settling inference from minimum_duration','rows':latency})
    all_prior=json.loads((OLD/'artifact-sha256.json').read_text())['files']
    for name,digest in all_prior.items():assert sha(OLD/name)==digest,name
    for name in ['pre-run-input-manifest.json','pre-run-implementation-manifest.json']:
        for path,digest in read(name)['files'].items():assert sha(HERE/path)==digest,(name,path)
    write('preservation.json',{'passed':True,'previous05_files_checked':len(all_prior),'previous05_manifest_sha256':sha(OLD/'artifact-sha256.json'),
                             'input_manifest_sha256':sha(HERE/'pre-run-input-manifest.json'),'implementation_manifest_sha256':sha(HERE/'pre-run-implementation-manifest.json')})
    write('runtime.json',{'python':sys.version,'executable':sys.executable,'numpy':numpy.__version__,'scipy':scipy.__version__,'platform':platform.platform()})
    print(json.dumps({k:v for k,v in summary.items() if k!='overview'},indent=2))
if __name__=='__main__':main()
