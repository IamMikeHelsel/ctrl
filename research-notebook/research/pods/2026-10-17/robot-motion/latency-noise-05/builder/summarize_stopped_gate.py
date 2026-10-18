"""Summarize existing frozen data only. No native calls or physical integration."""
from pathlib import Path
from fractions import Fraction as Q
from bisect import bisect_right
import csv, gzip, hashlib, json, platform, sys
import numpy, scipy
from make_references import state_at

HERE = Path(__file__).resolve().parent
ROBOT = HERE.parents[1]
METHODS = ['raw', 'ruckig', 'ruckig_min_08', 'fir']
CASES = ['hold_jitter', 'persistent_goal', 'sign_60ms',
         'irregular_alternation', 'seeded_random', 'biased_alternation']
LIMITS = [1e-8, 1e-8, 1e-10]

def read(name): return json.loads((HERE/name).read_text())
def write(name, value): (HERE/name).write_text(json.dumps(value, indent=2)+'\n')
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def key(row): return tuple(row[k] for k in ['method', 'case', 'rate', 'disturbance'])

def summarize_native_saved(schedules, exports):
    """Inspect the five already saved replays, preserving all failed criteria."""
    results = []
    for schedule in schedules:
        if schedule['method'] not in ['ruckig', 'ruckig_min_08']: continue
        identity = schedule['case']+'__'+schedule['method']
        path = HERE/'native'/(identity+'-output.json.gz')
        if not path.exists():
            results.append({'stream_method': identity, 'status': 'NOT RUN: stopped at prior audit failure'})
            continue
        native = json.loads(gzip.decompress(path.read_bytes()))
        plans = exports[identity]
        starts = [Q(x['start_exact']) for x in schedule['pieces']]
        residual = [0., 0., 0.]
        branches = []
        for sample in native['queries']:
            t = Q(sample['time'])
            piece = schedule['pieces'][min(bisect_right(starts,t)-1,len(starts)-1)]
            ref = state_at(piece,t)
            residual = [max(old,abs(sample[name]-value)) for old,name,value in zip(residual,['q','qv','qa'],ref[:3])]
            if abs(sample['jerk']-ref[3]) > 1e-8:
                branches.append({'time_s': sample['time'], 'native_jerk': sample['jerk'],
                                 'canonical_jerk': ref[3],
                                 'nearest_canonical_boundary_s': min(abs(float(t-s)) for s in starts)})
        current = [0., 0., 0.]
        assert len(plans) == len(native['commits'])
        for plan, native_commit in zip(plans, native['commits']):
            current = [max(old,abs(value-native_commit[name])) for old,value,name in zip(current,plan['plan']['input']['state'],['current_p','current_v','current_a'])]
        conditions = {'reference_state': all(v<=lim for v,lim in zip(residual,LIMITS)),
                      'retained_state': all(v<=lim for v,lim in zip(current,LIMITS)),
                      'jerk_branch_distance': all(x['nearest_canonical_boundary_s']<=1e-12 for x in branches)}
        results.append({'stream_method': identity, 'status': 'PASS' if all(conditions.values()) else 'FAIL',
                        'queries': len(native['queries']), 'commits': len(native['commits']),
                        'reference_max_abs_q_v_a': residual, 'current_max_abs_q_v_a': current,
                        'criteria': conditions, 'jerk_branch_disagreements': branches})
    write('native-replay-partial-audit.json', {
        'status': 'STOPPED; saved output inspection only; no native calls or physical reruns',
        'limits_q_v_a': LIMITS, 'jerk_branch_boundary_distance_limit_s': 1e-12,
        'completed_pairs': sum(x['status']!='NOT RUN: stopped at prior audit failure' for x in results),
        'passed_pairs': sum(x['status']=='PASS' for x in results),
        'failed_pairs': sum(x['status']=='FAIL' for x in results),
        'unrun_pairs': sum(x['status'].startswith('NOT RUN') for x in results), 'cases': results})

def main():
    rows = read('metrics.json')['rows']
    coarse = {key(r): r for r in rows if r['sample_step_s']==.001}
    fine = {key(r): r for r in rows if r['sample_step_s']==.0005}
    expected = {(m,c,r,w) for m in METHODS for c in CASES for r in [80,100,120] for w in [0.,.01]}
    assert len(rows)==288 and set(coarse)==set(fine)==expected
    schedules = read('reference-schedules.json')['schedules']
    exports = read('ruckig-primary-exports.json')
    summarize_native_saved(schedules, exports)
    fields = ['hold_peak_m', 'internal_error_peak_m', 'true_error_peak_m', 'shaping_error_peak_m',
              'actual_jerk_peak_m_s3', 'actual_jerk_energy_m2_s5', 'command_total_variation_m_s2',
              'largest_command_jump_m_s2', 'largest_actual_jerk_jump_m_s3', 'endpoint_error_m',
              'endpoint_v_m_s', 'endpoint_a_m_s2', 'settling_through_horizon_s']
    overview = []
    for case in CASES:
        for method in METHODS:
            subset = [r for r in fine.values() if r['case']==case and r['method']==method]
            ranges = {field: [min(r[field] for r in subset if r[field] is not None),
                              max(r[field] for r in subset if r[field] is not None)]
                      if any(r[field] is not None for r in subset) else None for field in fields}
            overview.append({'case': case, 'method': method,
                             'endpoint_passes': sum(r['endpoint_pass'] for r in subset),
                             'task_passes': sum(r['required_task_sample_pass'] for r in subset),
                             'hold_passes': sum(r['hold_band_pass'] is True for r in subset) if case!='persistent_goal' else None,
                             'ranges': ranges})
    table = []
    for row in overview:
        values = {k: row[k] for k in ['case','method','endpoint_passes','task_passes','hold_passes']}
        for field, span in row['ranges'].items():
            values[field+'_min'] = span[0] if span else ''
            values[field+'_max'] = span[1] if span else ''
        table.append(values)
    with (HERE/'comparison-table.csv').open('w',newline='') as file:
        writer = csv.DictWriter(file,fieldnames=list(table[0])); writer.writeheader(); writer.writerows(table)

    latency = []
    for method in METHODS:
        subset = [r for r in fine.values() if r['case']=='persistent_goal' and r['method']==method]
        duration = exports['persistent_goal__'+method][0]['plan']['duration'] if method.startswith('ruckig') else (.8 if method=='fir' else 0.)
        latency.append({'method': method, 'observation_s': .2, 'commit_s': .22,
                        'reference_duration_after_commit_s': duration,
                        'reference_planned_endpoint_time_s': .22+duration,
                        'physical_cases': [{'rate': r['rate'], 'disturbance': r['disturbance'],
                                            'settling_absolute_s': r['settling_through_horizon_s'],
                                            'settling_after_commit_s': r['settling_through_horizon_s']-.22,
                                            'jerk_energy_m2_s5': r['actual_jerk_energy_m2_s5'],
                                            'command_TV_m_s2': r['command_total_variation_m_s2']} for r in subset]})
    write('isolated-step-latency.json', {'status': 'canonical sampled results; minimum duration does not imply equal settling',
                                       'settling_definition': 'first sampled entry with position, velocity and acceleration within tolerance through fixed horizon',
                                       'rows': latency})
    scheduler = []
    for s in schedules:
        if s['method']!='fir': continue
        accepted = [x for x in s['admissions'] if x['outcome']=='accepted']
        scheduler.append({'case': s['case'],
                          'maximum_all_packet_age_at_commit_s': max(float(Q(x['commit_s'])-Q(x['observed_s'])) for x in s['admissions']),
                          'maximum_accepted_age_at_commit_s': max(float(Q(x['commit_s'])-Q(x['observed_s'])) for x in accepted),
                          'final_accepted_target_age_at_horizon_s': float(Q(s['horizon_exact'])-Q(accepted[-1]['observed_s'])),
                          'accepted': len(accepted), 'rejected': sum(x['outcome']=='jerk_rejected' for x in s['admissions']),
                          'stale': sum(x['outcome']=='stale_discard' for x in s['admissions'])})
    write('scheduler-audit.json', {'age_definition': 'time minus observation timestamp; common accepted trace across four methods', 'cases': scheduler})

    means = []
    for case in read('packets.json')['cases']:
        if case['id']=='persistent_goal': continue
        packets = case['packets']; assert Q(packets[-1]['target_m'])==0
        updates = packets[:-1]
        gaps = [Q(b['observed_s'])-Q(a['observed_s']) for a,b in zip(packets,packets[1:])]
        targets = [Q(p['target_m']) for p in updates]
        mean = sum(targets,Q(0))/len(targets)
        weighted = sum((g*t for g,t in zip(gaps,targets)),Q(0))/sum(gaps,Q(0))
        means.append({'case': case['id'], 'noise_updates': len(updates),
                      'episode_start_observed_s': packets[0]['observed_s'], 'zero_packet_observed_s': packets[-1]['observed_s'],
                      'episode_duration_s': str(sum(gaps,Q(0))), 'arithmetic_mean_m': str(mean),
                      'time_weighted_mean_m': str(weighted), 'time_weighted_mean_float_m': float(weighted),
                      'positive_target_dwell_s': str(sum((g for g,t in zip(gaps,targets) if t>0),Q(0))),
                      'negative_target_dwell_s': str(sum((g for g,t in zip(gaps,targets) if t<0),Q(0)))})
    irregular = next(x for x in means if x['case']=='irregular_alternation')
    assert irregular['arithmetic_mean_m']=='0' and irregular['time_weighted_mean_m']=='-1/2600'
    write('input-mean-audit.json', {'definition': 'Target held from each noise observation until the next observation, including final zero arrival. All commit times shift by the same .02 s, so the accepted-input episode means are equal.',
                                  'warning': 'irregular_alternation has zero arithmetic mean but nonzero dwell-weighted mean; biased_alternation is a deliberate bias limit; seeded_random has a nonzero realized sample mean.',
                                  'cases': means})

    duration_rows = read('native-duration-audit.json')['rows']
    minimum_rows = [r for r in duration_rows if r['requested_minimum_s']==.8]
    validations = read('ruckig-primary-validation.json')['cases']
    validation_rows = [x for group in validations.values() for x in group]
    assert len(minimum_rows)==246 and len(validation_rows)==492 and all(x['passed'] for x in validation_rows)
    ablation = read('fir-ablation-equality.json')['cases']
    assert len(ablation)==6 and all(x['all_prefixes_equal'] for x in ablation)
    native_summary = read('native-replay-partial-audit.json')
    summary = {'status': 'STOPPED_NATIVE_CLOCK_AUDIT; not an accepted complete numerical gate',
               'fixed_parameter_cases': 144, 'sampling_resolutions': 2, 'metric_rows': 288,
               'canonical_endpoint_passes': sum(x['endpoint_pass'] for x in fine.values()),
               'canonical_task_passes': sum(x['required_task_sample_pass'] for x in fine.values()),
               'maximum_actual_state_jump': max(x['actual_state_jump_max'] for x in fine.values()),
               'pre_run_same_input_native_plan_reconstructions_passed': len(validation_rows),
               'minimum_duration_plans': len(minimum_rows),
               'minimum_duration_actual_range_s': [min(x['actual_native_duration_s'] for x in minimum_rows),max(x['actual_native_duration_s'] for x in minimum_rows)],
               'minimum_duration_additional_blocked_adjustments': sum(x['excess_above_max_requested_and_independent_s']>0 for x in minimum_rows),
               'guarded_unguarded_equal_streams': len(ablation),
               'guarded_unguarded_equal_prefixes': sum(len(x['prefixes']) for x in ablation),
               'native_clock_completed_pairs': native_summary['completed_pairs'],
               'native_clock_passed_pairs': native_summary['passed_pairs'],
               'native_clock_failed_pairs': native_summary['failed_pairs'],
               'native_clock_unrun_pairs': native_summary['unrun_pairs'],
               'overview': overview}
    write('audit-summary.json',summary)

    preserved = {}; prior_manifests = {}
    for rel in ['lead-01','ultra-preflight-02','comparison-04/builder','comparison-04/grader']:
        folder = ROBOT/rel; manifest = folder/'artifact-sha256.json'
        for name, digest in json.loads(manifest.read_text())['files'].items():
            assert sha(folder/name)==digest,(rel,name)
            preserved[str(Path(rel)/name)] = digest
        prior_manifests[rel] = sha(manifest)
    for name in ['pre-run-input-manifest.json','pre-run-implementation-manifest.json']:
        for rel,digest in read(name)['files'].items(): assert sha(HERE/rel)==digest,(name,rel)
    write('preservation.json', {'passed': True, 'prior_files_checked': len(preserved), 'prior_files': preserved,
                                'prior_manifest_hashes': prior_manifests,
                                'input_manifest_sha256': sha(HERE/'pre-run-input-manifest.json'),
                                'implementation_manifest_sha256': sha(HERE/'pre-run-implementation-manifest.json')})
    write('runtime.json', {'python': sys.version, 'executable': sys.executable,
                           'numpy': numpy.__version__, 'scipy': scipy.__version__, 'platform': platform.platform(),
                           'scope': 'Read-only post-failure summary runtime; same local Python family as the physical run'})
    print(json.dumps({k:v for k,v in summary.items() if k!='overview'},indent=2))
    print('prior_files_preserved',len(preserved))

if __name__=='__main__': main()
