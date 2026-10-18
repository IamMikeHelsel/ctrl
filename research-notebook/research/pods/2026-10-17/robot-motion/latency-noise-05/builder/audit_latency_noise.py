"""Finite builder audits. Independent high-precision plant review remains separate."""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
import csv,gzip,hashlib,json,math,platform,subprocess,sys
import numpy,scipy
from make_references import state_at
HERE=Path(__file__).resolve().parent
ROBOT=HERE.parents[1]
METHODS=['raw','ruckig','ruckig_min_08','fir']
CASES=['hold_jitter','persistent_goal','sign_60ms','irregular_alternation','seeded_random','biased_alternation']
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def key(row):return tuple(row[k] for k in ['method','case','rate','disturbance'])

def native_audit(schedules,exports):
    folder=HERE/'native';folder.mkdir(exist_ok=True);results=[]
    for schedule in schedules:
        if schedule['method'] not in ['ruckig','ruckig_min_08']:continue
        identity=schedule['case']+'__'+schedule['method'];plans=exports[identity]
        minimum=.8 if schedule['method']=='ruckig_min_08' else 0.
        commits=[(float(Q(x['commit_rational'])),x['plan']['input']['target']) for x in plans]
        horizon=schedule['horizon'];queries={i/2000 for i in range(round(horizon*2000)+1)}
        for p in schedule['pieces']:
            for name in ['start','end']:
                t=p[name];queries.add(t)
                if t>0:queries.add(math.nextafter(t,-math.inf))
                if 0<t<horizon:queries.add(math.nextafter(t,math.inf))
        queries=sorted(t for t in queries if 0<=t<=horizon)
        inputs=str(len(commits))+'\n'+''.join(f'{t:.17g} {target:.17g}\n' for t,target in commits)+str(len(queries))+'\n'+''.join(f'{t:.17g}\n' for t in queries)
        (folder/(identity+'-input.txt')).write_text(inputs)
        result=subprocess.run([str(HERE/'.cache/native_replay'),str(minimum)],input=inputs,text=True,capture_output=True,check=True)
        native=json.loads(result.stdout);assert [x['time'] for x in native['queries']]==queries
        (folder/(identity+'-output.json.gz')).write_bytes(gzip.compress(result.stdout.encode(),mtime=0))
        starts=[Q(x['start_exact']) for x in schedule['pieces']];residual=[0.,0.,0.];branches=[]
        for sample in native['queries']:
            t=Q(sample['time']);p=schedule['pieces'][min(bisect_right(starts,t)-1,len(starts)-1)];reference=state_at(p,t)
            residual=[max(old,abs(sample[name]-value)) for old,name,value in zip(residual,['q','qv','qa'],reference[:3])]
            if abs(sample['jerk']-reference[3])>1e-8:
                distance=min(abs(float(t-s)) for s in starts)
                branches.append({'time_s':sample['time'],'native_jerk':sample['jerk'],'canonical_jerk':reference[3],'nearest_boundary_s':distance})
        current=[0.,0.,0.]
        for plan,native_commit in zip(plans,native['commits']):
            current=[max(old,abs(value-native_commit[name])) for old,value,name in zip(current,plan['plan']['input']['state'],['current_p','current_v','current_a'])]
        assert all(value<=limit for value,limit in zip(residual,[1e-8,1e-8,1e-10])),(identity,residual)
        assert all(value<=limit for value,limit in zip(current,[1e-8,1e-8,1e-10])),(identity,current)
        assert all(x['nearest_boundary_s']<=1e-12 for x in branches),(identity,branches)
        results.append({'stream_method':identity,'minimum_duration_s':minimum,'queries':len(queries),'commits':len(commits),'reference_max_abs_q_v_a':residual,'current_max_abs_p_v_a':current,'jerk_branch_disagreements':branches,'passed':True})
    write('native-replay-audit.json',{'passed':True,'status':'builder native at_time replay; not independent physical validation','cases':results})

def main():
    rows=json.loads((HERE/'metrics.json').read_text())['rows']
    coarse={key(r):r for r in rows if r['sample_step_s']==.001};fine={key(r):r for r in rows if r['sample_step_s']==.0005}
    expected={(m,c,r,w) for m in METHODS for c in CASES for r in [80,100,120] for w in [0.,.01]}
    assert set(coarse)==set(fine)==expected
    fields=['hold_peak_m','internal_error_peak_m','actual_jerk_peak_m_s3','actual_jerk_energy_m2_s5','command_total_variation_m_s2','endpoint_error_m','endpoint_v_m_s','endpoint_a_m_s2','settling_through_horizon_s']
    refinement=[]
    for identity,a in coarse.items():
        b=fine[identity]
        for field in ['endpoint_pass','hold_band_pass','internal_tube_sample_pass','required_task_sample_pass']:assert a[field]==b[field],(identity,field)
        refinement.append({'case':identity,'changes':{field:{'coarse':a[field],'fine':b[field],'absolute_change':abs(a[field]-b[field]),'relative_change_to_fine':abs(a[field]-b[field])/max(abs(b[field]),1e-30)} for field in fields if a[field] is not None and b[field] is not None}})
    maxima={field:{'max_absolute_change':max(x['changes'][field]['absolute_change'] for x in refinement if field in x['changes']),'max_relative_change_to_fine':max(x['changes'][field]['relative_change_to_fine'] for x in refinement if field in x['changes'])} for field in fields}
    states={x['case_id']:x['states'] for x in json.loads((HERE/'event-states.json').read_text())};state_error=[0.,0.,0.]
    for name,values in states.items():
        if not name.endswith('dt1000us'):continue
        other=states[name[:-8]+'dt500us'];assert len(values)==len(other)
        for a,b in zip(values,other):
            assert a['time_exact']==b['time_exact']
            state_error=[max(old,abs(a[k]-b[k])) for old,k in zip(state_error,['x','v','a'])]
    write('refinement.json',{'status':'same builder, two sampling resolutions; no independent numerical claim','all_decisions_unchanged':True,'maximum_event_state_changes':state_error,'maximum_metric_changes':maxima,'cases':refinement})
    oldrows=json.loads((ROBOT/'comparison-04/builder/metrics.json').read_text())['rows'];matched=0
    for old in oldrows:
        if old['case'] not in ['hold_jitter','persistent_goal']:continue
        new=(coarse if old['sample_step_s']==.001 else fine)[key(old)]
        assert new==old,(key(old),{k:(old[k],new[k]) for k in old if old[k]!=new[k]})
        matched+=1
    write('original-case-regression.json',{'passed':True,'original_metric_rows_identical':matched,'parameter_cases':matched//2,'scope':'three unchanged methods on the original two copied streams at both resolutions'})
    schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules'];exports=json.loads((HERE/'ruckig-primary-exports.json').read_text())
    native_audit(schedules,exports)
    overview=[]
    for case in CASES:
        for method in METHODS:
            subset=[r for r in fine.values() if r['case']==case and r['method']==method]
            ranges={field:[min(r[field] for r in subset if r[field] is not None),max(r[field] for r in subset if r[field] is not None)] if any(r[field] is not None for r in subset) else None for field in fields}
            overview.append({'case':case,'method':method,'endpoint_passes':sum(r['endpoint_pass'] for r in subset),'task_passes':sum(r['required_task_sample_pass'] for r in subset),'hold_passes':sum(r['hold_band_pass'] is True for r in subset) if case!='persistent_goal' else None,'ranges':ranges})
    latency=[]
    for method in METHODS:
        subset=[r for r in fine.values() if r['case']=='persistent_goal' and r['method']==method]
        duration=exports['persistent_goal__'+method][0]['plan']['duration'] if method.startswith('ruckig') else (.8 if method=='fir' else 0.)
        latency.append({'method':method,'observation_s':.2,'commit_s':.22,'reference_duration_after_commit_s':duration,'reference_planned_endpoint_time_s':.22+duration,
                        'actual_settling_through_horizon_s':[r['settling_through_horizon_s'] for r in subset],
                        'physical_cases':[{'rate':r['rate'],'disturbance':r['disturbance'],'settling_s':r['settling_through_horizon_s'],'jerk_energy':r['actual_jerk_energy_m2_s5'],'command_TV':r['command_total_variation_m_s2']} for r in subset]})
    write('isolated-step-latency.json',{'status':'actual native duration and sampled physical settling; minimum duration does not imply equal settling','rows':latency})
    scheduler=[]
    for s in schedules:
        if s['method']!='fir':continue
        accepted=[x for x in s['admissions'] if x['outcome']=='accepted']
        scheduler.append({'case':s['case'],'maximum_all_packet_age_at_commit_s':max(float(Q(x['commit_s'])-Q(x['observed_s'])) for x in s['admissions']),
                          'maximum_accepted_age_at_commit_s':max(float(Q(x['commit_s'])-Q(x['observed_s'])) for x in accepted),'final_accepted_target_age_at_horizon_s':float(Q(s['horizon_exact'])-Q(accepted[-1]['observed_s'])),
                          'accepted':len(accepted),'rejected':sum(x['outcome']=='jerk_rejected' for x in s['admissions']),'stale':sum(x['outcome']=='stale_discard' for x in s['admissions'])})
    write('scheduler-audit.json',{'age_definition':'time minus packet observation; final age is the latest accepted target at the fixed horizon','cases':scheduler})
    preserved={}
    for path in ['lead-01','ultra-preflight-02','comparison-04/builder','comparison-04/grader']:
        folder=ROBOT/path;manifest=json.loads((folder/'artifact-sha256.json').read_text())
        for name,digest in manifest['files'].items():
            assert sha(folder/name)==digest,(path,name)
            preserved[str(Path(path)/name)]=digest
    for name in ['pre-run-input-manifest.json','pre-run-implementation-manifest.json']:
        manifest=json.loads((HERE/name).read_text())
        for path,digest in manifest['files'].items():assert sha(HERE/path)==digest,(name,path)
    write('preservation.json',{'passed':True,'prior_files':preserved,'input_manifest_sha256':sha(HERE/'pre-run-input-manifest.json'),'implementation_manifest_sha256':sha(HERE/'pre-run-implementation-manifest.json')})
    write('runtime.json',{'python':sys.version,'executable':sys.executable,'numpy':numpy.__version__,'scipy':scipy.__version__,'platform':platform.platform()})
    summary={'status':'builder numerical audit complete; independent high-precision review pending','fixed_parameter_cases':144,'resolutions':2,'endpoint_passes':sum(x['endpoint_pass'] for x in fine.values()),'task_passes':sum(x['required_task_sample_pass'] for x in fine.values()),'maximum_actual_state_jump':max(x['actual_state_jump_max'] for x in fine.values()),'overview':overview}
    write('audit-summary.json',summary)
    table=[]
    for row in overview:
        values={k:row[k] for k in ['case','method','endpoint_passes','task_passes','hold_passes']}
        for field,span in row['ranges'].items():
            values[field+'_min']=span[0] if span else '';values[field+'_max']=span[1] if span else ''
        table.append(values)
    with (HERE/'comparison-table.csv').open('w',newline='') as file:
        writer=csv.DictWriter(file,fieldnames=list(table[0]));writer.writeheader();writer.writerows(table)
    print(json.dumps({'endpoint_passes':summary['endpoint_passes'],'task_passes':summary['task_passes'],'maximum_event_state_refinement':state_error,'original_metric_rows_identical':matched,'prior_files_preserved':len(preserved),'overview':overview},indent=2))

if __name__=='__main__':main()
