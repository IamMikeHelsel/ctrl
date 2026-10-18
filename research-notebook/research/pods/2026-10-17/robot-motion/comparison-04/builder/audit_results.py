from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
import csv,gzip,hashlib,json,math,platform,subprocess,sys
import numpy,scipy
from make_references import state_at

HERE=Path(__file__).resolve().parent
ROBOT=HERE.parents[1]
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def key(row):return tuple(row[k] for k in ['method','case','rate','disturbance'])

def main():
    rows=json.loads((HERE/'metrics.json').read_text())['rows']
    coarse={key(r):r for r in rows if r['sample_step_s']==.001}
    fine={key(r):r for r in rows if r['sample_step_s']==.0005}
    expected={(m,c,r,w) for m in ['raw','ruckig','fir'] for c in ['hold_jitter','persistent_goal','revised_goal','late_and_stale'] for r in [80,100,120] for w in [0.,.01]}
    assert set(coarse)==set(fine)==expected
    metrics=['actual_jerk_peak_m_s3','actual_jerk_energy_m2_s5','command_total_variation_m_s2','internal_error_peak_m','hold_peak_m','endpoint_error_m','endpoint_v_m_s','endpoint_a_m_s2','settling_through_horizon_s']
    differences=[]
    for case,a in coarse.items():
        b=fine[case]
        for field in ['endpoint_pass','hold_band_pass','internal_tube_sample_pass','required_task_sample_pass']:assert a[field]==b[field]
        differences.append({'case':case,'changes':{field:{'coarse':a[field],'fine':b[field],'absolute_change':abs(b[field]-a[field]),'relative_change_to_fine':abs(b[field]-a[field])/max(abs(b[field]),1e-30)} for field in metrics if a[field] is not None and b[field] is not None}})
    max_changes={field:{'max_absolute_change':max(x['changes'][field]['absolute_change'] for x in differences if field in x['changes']),
                        'max_relative_change_to_fine':max(x['changes'][field]['relative_change_to_fine'] for x in differences if field in x['changes'])} for field in metrics}
    state_sets=json.loads((HERE/'event-states.json').read_text())
    state_map={x['case_id']:x['states'] for x in state_sets}
    maxima=[0.,0.,0.]
    for name,states in state_map.items():
        if not name.endswith('dt1000us'):continue
        other=state_map[name[:-8]+'dt500us']
        assert len(states)==len(other)
        for a,b in zip(states,other):
            assert a['time_exact']==b['time_exact']
            maxima=[max(old,abs(a[k]-b[k])) for old,k in zip(maxima,['x','v','a'])]
    write('refinement.json',{'status':'same builder, two sampling resolutions; not independent validation','fixed_parameter_cases':72,'all_pass_fail_decisions_unchanged':True,'maximum_event_state_change_x_v_a':maxima,'maximum_metric_changes':max_changes,'cases':differences})

    schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules']
    frozen=json.loads((HERE/'frozen-fixed-streams.json').read_text())
    scheduler=[]
    for case in frozen['cases']:
        if case['role']!='primary':continue
        scheduled=next(s for s in schedules if s['case']==case['id'])
        accepted=[x for x in scheduled['admissions'] if x['outcome']=='accepted']
        scheduler.append({'case':case['id'],'admission_equals_execution':True,'additional_future_queue_s':0,
                          'maximum_all_packet_age_at_commit_s':max(float(Q(x['commit_s'])-Q(x['observed_s'])) for x in scheduled['admissions']),
                          'maximum_accepted_packet_age_at_commit_s':max(float(Q(x['commit_s'])-Q(x['observed_s'])) for x in accepted),
                          'final_accepted_target_age_at_horizon_s':float(Q(case['end_s'])-Q(accepted[-1]['observed_s'])),
                          'accepted_count':len(accepted),'full_admission_transcript':scheduled['admissions']})
    write('scheduler-audit.json',{'age_definition':'Age is time minus packet observation timestamp. The all-packet commit maximum includes discarded stale packets. Accepted commit age and final accepted-target age are reported separately. Age does not imply truth freshness or task progress.','cases':scheduler})
    schedule=next(s for s in schedules if s['case']=='hold_jitter' and s['method']=='ruckig')
    biggest=max((r for r in fine.values() if r['case']=='hold_jitter' and r['method']=='ruckig'),key=lambda x:x['hold_peak_m'])
    stem=f"hold_jitter__ruckig__r{biggest['rate']}__w{int(round(biggest['disturbance']*100)):02d}__dt500us"
    with gzip.open(HERE/'traces'/(stem+'.csv.gz'),'rt') as file:
        peak=max(csv.DictReader(file),key=lambda row:abs(float(row['x'])))
    peak_time=Q(peak['time_exact'])
    original=json.loads((HERE/'ruckig-primary-exports.json').read_text())['hold_jitter']
    commits=[(float(Q(x['commit_rational'])),x['plan']['input']['target']) for x in original]
    queries={i/2000 for i in range(5001)}|{float(peak_time)}
    for piece in schedule['pieces']:
        for field in ['start','end']:
            t=piece[field];queries.add(t)
            if t>0:queries.add(math.nextafter(t,-math.inf))
            if 0<t<2.5:queries.add(math.nextafter(t,math.inf))
    queries=sorted(t for t in queries if 0<=t<=2.5)
    inputs=str(len(commits))+'\n'+''.join(f'{t:.17g} {target:.17g}\n' for t,target in commits)+str(len(queries))+'\n'+''.join(f'{t:.17g}\n' for t in queries)
    (HERE/'native-hold-replay-input.txt').write_text(inputs)
    run=subprocess.run([str(HERE/'.cache/native_replay')],input=inputs,text=True,capture_output=True,check=True)
    native=json.loads(run.stdout);write('native-hold-replay.json',native)
    assert [row['time'] for row in native['queries']]==queries
    starts=[Q(p['start_exact']) for p in schedule['pieces']]
    reference_residual=[0.,0.,0.];jerk_mismatches=[]
    for row in native['queries']:
        t=Q(row['time']);piece=schedule['pieces'][min(bisect_right(starts,t)-1,len(starts)-1)]
        q=state_at(piece,t)
        reference_residual=[max(old,abs(row[k]-v)) for old,k,v in zip(reference_residual,['q','qv','qa'],q[:3])]
        if abs(row['jerk']-q[3])>1e-8:
            near=min(abs(float(t-Q(p['start_exact']))) for p in schedule['pieces'])
            jerk_mismatches.append({'time':row['time'],'native_jerk':row['jerk'],'replay_jerk':q[3],'distance_to_replay_boundary_s':near})
    commit_residual=[0.,0.,0.]
    for canonical,nat in zip(original,native['commits']):
        commit_residual=[max(old,abs(x-nat[k])) for old,x,k in zip(commit_residual,canonical['plan']['input']['state'],['current_p','current_v','current_a'])]
    assert all(x<=limit for x,limit in zip(reference_residual,[1e-8,1e-8,1e-10]))
    assert all(x<=limit for x,limit in zip(commit_residual,[1e-8,1e-8,1e-10]))
    assert all(x['distance_to_replay_boundary_s']<=1e-12 for x in jerk_mismatches)
    all_plans=list(json.loads((HERE/'ruckig-smoke-exports.json').read_text()).values())
    primary=json.loads((HERE/'ruckig-primary-exports.json').read_text())
    all_plans += [x['plan'] for case in primary.values() for x in case]
    timing_difference=Q(0);tiny=[]
    for index,plan in enumerate(all_plans):
        cumulative=Q(0)
        for phase in plan['phases']:
            if phase['kind']!='main':continue
            cumulative+=Q(phase['duration'])
            timing_difference=max(timing_difference,abs(cumulative-Q(phase['native_t_sum'])))
            if 0<phase['duration']<1e-12:tiny.append({'plan_index':index,'phase':phase})
    diagnostic={'status':'builder native reference replay; independent physical replay remains open',
                'frozen_input_case':next(c for c in frozen['cases'] if c['id']=='hold_jitter'),
                'full_admission_transcript':schedule['admissions'],
                'largest_ruckig_hold_excursion':{'parameter_case':key(biggest),'trace':str(Path('traces')/(stem+'.csv.gz')),'row':peak},
                'native_current_states_at_every_commit':native['commits'],
                'canonical_current_states_at_every_commit':[{'commit':x['commit_rational'],'state':x['plan']['input']['state'],'target':x['plan']['input']['target']} for x in original],
                'executed_reference_pieces_within_50ms_of_peak':[p for p in schedule['pieces'] if Q(p['end_exact'])>=peak_time-Q(1,20) and Q(p['start_exact'])<=peak_time+Q(1,20)],
                'canonical_reference_vs_native_max_abs_q_v_a':reference_residual,'canonical_vs_native_commit_state_max_abs_p_v_a':commit_residual,
                'pointwise_jerk_branch_disagreements_near_rounding_boundaries':jerk_mismatches,
                'clock_interpretation':'Primary replay adds the native rounded cumulative boundary to rational commit time. Native diagnostic uses double absolute clocks and native subtraction. They are not bit-identical. Branch differences are retained; state errors are bounded only by the recorded finite tests.',
                'maximum_native_t_sum_minus_exact_sum_of_binary_durations_s':str(timing_difference),'positive_phases_shorter_than_1ps':tiny}
    write('hold-jitter-diagnostic.json',diagnostic)
    preservation={}
    for name in ['lead-01','ultra-preflight-02']:
        folder=ROBOT/name;manifest=json.loads((folder/'artifact-sha256.json').read_text())
        for rel,expected_hash in manifest['files'].items():
            assert sha(folder/rel)==expected_hash,(name,rel)
            preservation[str(Path(name)/rel)]=expected_hash
    for name in ['fixed-streams.json','reference-checks.json','reference-enclosures.json']:assert sha(HERE/('frozen-'+name))==sha(ROBOT/'lead-01'/name)
    write('input-preservation.json',{'passed':True,'files':preservation,'lead_manifest_sha256':sha(ROBOT/'lead-01/artifact-sha256.json'),'preflight_manifest_sha256':sha(ROBOT/'ultra-preflight-02/artifact-sha256.json')})
    write('runtime.json',{'python':sys.version,'executable':sys.executable,'numpy':numpy.__version__,'scipy':scipy.__version__,'platform':platform.platform()})
    overview=[]
    for case in ['hold_jitter','persistent_goal','revised_goal','late_and_stale']:
        for method in ['raw','ruckig','fir']:
            rr=[r for r in fine.values() if r['case']==case and r['method']==method]
            fields=['hold_peak_m','internal_error_peak_m','actual_jerk_peak_m_s3','actual_jerk_energy_m2_s5','command_total_variation_m_s2','settling_through_horizon_s','endpoint_error_m','endpoint_v_m_s','endpoint_a_m_s2']
            overview.append({'case':case,'method':method,'endpoint_pass_count':sum(r['endpoint_pass'] for r in rr),'required_task_pass_count':sum(r['required_task_sample_pass'] for r in rr),'internal_tube_pass_count':sum(r['internal_tube_sample_pass'] for r in rr),'ranges':{k:[min(r[k] for r in rr),max(r[k] for r in rr)] for k in fields}})
    result={'status':'builder finite numerical audit complete; independent high-precision review pending','fixed_cases':72,'resolutions':2,'endpoint_passes':sum(r['endpoint_pass'] for r in fine.values()),'required_task_passes':sum(r['required_task_sample_pass'] for r in fine.values()),'maximum_actual_state_event_jump':max(r['actual_state_jump_max'] for r in fine.values()),'overview':overview}
    write('audit-summary.json',result)
    print(json.dumps({'endpoint_passes':result['endpoint_passes'],'required_task_passes':result['required_task_passes'],'max_event_state_refinement':maxima,'max_metric_refinement':max_changes,'native_reference_residual':reference_residual,'native_commit_residual':commit_residual,'native_jerk_branch_disagreements':len(jerk_mismatches),'peak_hold_time':str(peak_time),'preserved_files':len(preservation)},indent=2))

if __name__=='__main__':main()
