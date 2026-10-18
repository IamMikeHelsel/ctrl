"""Read-only analysis of the frozen moving-goal data; no plant/native calls."""
from pathlib import Path
from fractions import Fraction as Q
import csv,hashlib,json,datetime
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')

def main():
    data=json.loads((HERE/'data-sha256.json').read_text())
    for n,h in data['files'].items():assert sha(HERE/n)==h,n
    rows=json.loads((HERE/'metrics.json').read_text())['rows']; assert len(rows)==144
    fine=[r for r in rows if r['sample_step_s']==.0005];coarse=[r for r in rows if r['sample_step_s']==.001]
    identity=lambda r:(r['case'],r['method'],r['rate'],r['disturbance'])
    cmap={identity(r):r for r in coarse}; differences=[];decision_changes=[]
    flagkeys=['endpoint_position_pass','endpoint_velocity_pass','endpoint_acceleration_pass','endpoint_pass','initial_response_pass','deadline_and_remain_sample_pass','causal_deadline_service_pass','all_authoritative_requests_admitted','reference_limits_numerical_pass','overall_valid_task_numerical_pass']
    numerickeys=['endpoint_error_m','endpoint_v_m_s','endpoint_a_m_s2','initial_progress_m','internal_error_peak_m','actual_jerk_peak_m_s3','actual_jerk_energy_m2_s5','command_continuous_TV_m_s2','command_jump_TV_m_s2','command_total_variation_m_s2']
    for f in fine:
        c=cmap[identity(f)]
        for k in flagkeys:
            if c[k]!=f[k]:decision_changes.append({'case':identity(f),'metric':k,'coarse':c[k],'fine':f[k]})
        deltas={k:abs(c[k]-f[k]) for k in numerickeys}
        deltas['settling_time_s']=None if c['settling_through_horizon_s'] is None or f['settling_through_horizon_s'] is None else abs(c['settling_through_horizon_s']-f['settling_through_horizon_s'])
        differences.append({'case':identity(f),'absolute_deltas':deltas})
    worst={k:max((r['absolute_deltas'][k] for r in differences if r['absolute_deltas'][k] is not None),default=None) for k in numerickeys+['settling_time_s']}
    write('refinement.json',{'decision_changes':decision_changes,'maximum_absolute_deltas':worst,'pairs':differences,'scope':'Fixed1ms/.5ms finite numerical consistency; no adaptive grid or continuous-time proof.'})
    assert not decision_changes
    groups=[]
    for case in dict.fromkeys(r['case'] for r in fine):
        for method in dict.fromkeys(r['method'] for r in fine):
            g=[r for r in fine if r['case']==case and r['method']==method];settle=[r['settling_through_horizon_s'] for r in g if r['settling_through_horizon_s'] is not None]
            groups.append({'case':case,'method':method,'cases':len(g),
                **{k+'_count':sum(r[k] is True for r in g) for k in ['endpoint_pass','initial_response_pass','deadline_and_remain_sample_pass','causal_deadline_service_pass','all_authoritative_requests_admitted','reference_limits_numerical_pass','overall_valid_task_numerical_pass']},
                'absolute_settling_min_s':min(settle) if settle else None,'absolute_settling_max_s':max(settle) if settle else None,
                'maximum_deadline_abs_goal_error_mm':max(abs(r['endpoint_error_m']) for r in g)*1000,
                'reference_acceleration_peak_m_s2':g[0]['reference_peak_acceleration_critical_m_s2'],
                'initial_progress_min_mm':min(r['initial_progress_m'] for r in g)*1000,
                'actual_jerk_squared_integral_min_m2_s5':min(r['actual_jerk_energy_m2_s5'] for r in g),
                'actual_jerk_squared_integral_max_m2_s5':max(r['actual_jerk_energy_m2_s5'] for r in g),
                'command_TV_min_m_s2':min(r['command_total_variation_m_s2'] for r in g),
                'command_TV_max_m_s2':max(r['command_total_variation_m_s2'] for r in g)})
    with (HERE/'comparison-table.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(groups[0]));writer.writeheader();writer.writerows(groups)
    native=json.loads((HERE/'native-pre-run-gate.json').read_text())
    exports=json.loads((HERE/'ruckig-primary-exports.json').read_text())
    clock=max(abs(Q(r['native_minus_scheduler_time_exact'])) for plans in exports.values() for r in plans)
    summary={'status':'Builder summary; independent physical review pending.','parameter_cases':72,'resolutions':2,'saved_traces':144,'unique_physical_parameter_cases':54,'A_B_identical_trace_pairs':36,
             'fine_endpoint_pass':sum(r['endpoint_pass'] for r in fine),'fine_deadline_and_remain_pass':sum(r['deadline_and_remain_sample_pass'] for r in fine),'fine_overall_valid_task_pass':sum(r['overall_valid_task_numerical_pass'] for r in fine),
             'fine_initial_response_pass':sum(r['initial_response_pass'] for r in fine),
             'valid_per_method':{m:sum(r['overall_valid_task_numerical_pass'] for r in fine if r['method']==m) for m in ['ruckig','ruckig_min_08','fir']},
             'maximum_sampled_internal_error_mm':max(r['internal_error_peak_m'] for r in rows)*1000,
             'maximum_physical_state_jump':max(r['actual_state_jump_max'] for r in rows),
             'native_plans':16,'native_histories':8,'native_queries':sum(c['queries'] for c in native['cases']),
             'native_q_v_a_max_residual':[max(c['reference_max_abs_q_v_a'][i] for c in native['cases']) for i in range(3)],
             'native_jerk_branch_differences':sum(len(c['jerk_branch_disagreements']) for c in native['cases']),
             'maximum_native_clock_offset_exact_s':str(clock),'maximum_native_clock_offset_s':float(clock),
             'groups':groups,'refinement_maximum_absolute_deltas':worst,'refinement_decision_changes':decision_changes,
             'buffered_example_r100_w01':[r for r in fine if r['case']=='return_late_buffered' and r['rate']==100 and r['disturbance']==.01],
             'rejected_execution_label':'For reverse_far_guard FIR, revision_execution_s is the requested rejected execution instant. No revision event was added; the old accepted goal remains+20mm.'}
    write('analysis-summary.json',summary)
    # Check the complete earlier builder freezes, plus all08 input/data freezes.
    root=HERE.parents[1];preserved=[]
    for rel in ['latency-noise-05/builder','native-execution-06/builder']:
        folder=root/rel;manifest=folder/'artifact-sha256.json';old=json.loads(manifest.read_text());n=0
        for name,digest in old['files'].items():
            expected=digest if isinstance(digest,str) else digest['sha256']
            assert sha(folder/name)==expected,(rel,name);n+=1
        preserved.append({'path':rel,'manifest_sha256':sha(manifest),'files_verified':n})
    for n in ['pre-run-input-manifest.json','pre-run-implementation-manifest.json','data-sha256.json']:
        man=json.loads((HERE/n).read_text())
        for name,h in man['files'].items():assert sha(HERE/name)==h,(n,name)
    write('preservation.json',{'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'earlier_builder_freezes':preserved,'all08_input_implementation_data_bindings_unchanged':True})
    print(json.dumps({k:summary[k] for k in ['fine_endpoint_pass','fine_overall_valid_task_pass','valid_per_method','refinement_decision_changes','refinement_maximum_absolute_deltas']},indent=2))

if __name__=='__main__':main()
