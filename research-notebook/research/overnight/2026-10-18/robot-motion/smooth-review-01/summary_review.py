"""Compare reports and figure aggregation to independent 80-digit replay."""
from pathlib import Path
from fractions import Fraction as F
import csv,gzip,hashlib,json,math

HERE=Path(__file__).resolve().parent
B=HERE.parent/'smooth-baseline-01'; BASE=HERE.parent/'builder-03';OLD=HERE.parent/'critic-03'
def read(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def check_manifest(folder,name,digest):
    assert sha(folder/name)==digest
    manifest=read(folder/name)
    for n,v in manifest['files'].items():assert sha(folder/n)==(v['sha256'] if isinstance(v,dict) else v),(folder,n)
    return len(manifest['files'])
checked={}
checked['root']=check_manifest(B,'artifact-sha256.json','14b028f05727b6459b30e63d84162fc49de1fdeb65c1a9327d30468149afd3c9')
checked['baseline']=check_manifest(BASE,'artifact-sha256.json','abfc9ca6da02e5cbec77b4019e8f356c80d612f65bea3fcb3e7b227ec1cf6d58')
checked['prior_independent_review']=check_manifest(OLD,'artifact-sha256.json','2b3cc05bf3e9374bb21478c486424afca21b5d67b76e0bd9551747a9ed5b3660')
new=read(HERE/'physical-review.json');old=read(OLD/'physical-review.json')
assert new['passed'] and old['passed']
# Apply tighter, dimensional reporting tolerances than the copied review's final
# common threshold. These are numerical comparison tolerances, not error bounds.
for k,v in new['row_max_error'].items():
    lim=1e-11 if k in ['actual_jerk','u_derivative_piecewise','reference_snap_piecewise'] else 1e-12
    assert v<lim,(k,v,lim)
assert max(new['metric_max_error'].values())<1e-10
assert max(new['event_max_error'].values())<1e-10
def identifier(r):return f"{r['case']}__{r['method']}__r{r['rate']}__w{int(r['disturbance']*100):02d}__dt{int(r['sample_step_s']*1000000)}us"
byid={r['case_id']:r for source in [old,new] for r in source['cases']}
saved=read(B/'metrics.json')['rows']+read(BASE/'metrics.json')['rows']
rows=[]
for r in saved:
    measured=byid[identifier(r)]['metrics']
    rows.append({**r,**measured})
summary=read(B/'analysis-summary.json');fields=0;maxdiff=0.
def close(a,b):
    global fields,maxdiff
    fields+=1
    if isinstance(a,(int,bool)) and isinstance(b,(int,bool)):assert a==b;return
    d=abs(a-b);maxdiff=max(maxdiff,d);assert d<1e-9,(a,b,d)
for g in summary['groups']:
    selected=[r for r in rows if r['method']==g['method'] and r['case']==g['case'] and r['sample_step_s']==.0005]
    close(len(selected),g['cases']);assert len(selected)==6
    close(sum(r['revision_accepted'] for r in selected),g['accepted_requests'])
    close(sum(r['full_task_pass'] for r in selected),g['full_task_passes'])
    for k,bounds in g['ranges'].items():
        close(min(r[k] for r in selected),bounds[0]);close(max(r[k] for r in selected),bounds[1])
for group in summary['paired_candidate_ratios']:
    assert len(group['pairs'])==6
    for p in group['pairs']:
        common=lambda r:r['case']=='return_generous' and r['sample_step_s']==.0005 and r['rate']==p['rate'] and r['disturbance']==p['disturbance']
        a=next(r for r in rows if common(r) and r['method']=='smooth_n90_cap10mm')
        b=next(r for r in rows if common(r) and r['method']==group['baseline'])
        for k,v in p['ratios'].items():close(a[k]/b[k],v)
for group in summary['output_grid_checks']:
    selected=[r for r in rows if r['method']==group['method'] and r['sample_step_s']==.0005]
    paired=[]
    for a in selected:
        b=next(r for r in rows if r['method']==a['method'] and r['case']==a['case'] and r['rate']==a['rate'] and r['disturbance']==a['disturbance'] and r['sample_step_s']==.001)
        paired.append((a,b))
    assert group['task_decisions_unchanged']==all(a['full_task_pass']==b['full_task_pass'] for a,b in paired)
    for k,v in group['maximum_absolute_metric_differences'].items():close(max(abs(a[k]-b[k]) for a,b in paired),v)
# Recheck the CSV's rounded table independently.
with (B/'comparison-table.csv').open() as f:table=list(csv.DictReader(f))
assert len(table)==len(summary['groups'])
for t in table:
    selected=[r for r in rows if r['case']==t['task'] and r['method']==t['method'] and r['sample_step_s']==.0005]
    close(int(t['accepted']),sum(r['revision_accepted'] for r in selected));close(int(t['full_task_passes']),sum(r['full_task_pass'] for r in selected))
    for label,key,scale in [('jerk_integral','suffix_until_horizon_jerk_energy_m2_s5',1),('excursion','suffix_until_horizon_extra_forward_excursion_m',1000),('peak_jerk','suffix_until_horizon_actual_jerk_peak_m_s3',1)]:
        for extremum,func in [('min',min),('max',max)]:
            column=label+'_'+extremum+('_mm' if label=='excursion' else '')
            close(float(t[column]),scale*func(r[key] for r in selected))
# Compare every new trace prefix to each prior controller. This checks both the
# numerical states and the independently replayed high-precision prefix digest.
prefix_fields=['time_exact','side','q','qv','qa','reference_jerk','reference_snap_piecewise','x','v','a','u','actual_jerk','truth','x_minus_q','x_minus_truth']
cache={};prefixes=0
def prefix(path):
    with gzip.open(path,'rt') as f:return [{k:r[k] for k in prefix_fields} for r in csv.DictReader(f) if F(r['time_exact'])<F(13,25) or (F(r['time_exact'])==F(13,25) and r['side']=='left')]
for r in read(B/'metrics.json')['rows']:
    caseid=identifier(r);pr=prefix(B/'traces'/(caseid+'.csv.gz'))
    for method in ['fir_checked','native_fast','native_matched']:
        br={**r,'case':'return_generous','method':method};bid=identifier(br)
        if bid not in cache:cache[bid]=prefix(BASE/'traces'/(bid+'.csv.gz'))
        assert pr==cache[bid]
        assert byid[caseid]['prefix_sha256_55_digits']==byid[bid]['prefix_sha256_55_digits']
        prefixes+=1
ss=read(B/'reference-schedules.json')['schedules'];bs=read(BASE/'reference-schedules.json')['schedules']
fallback=next(s for s in bs if s['method']=='fir_checked' and s['case']=='return_tight')
for s in ss:
    original=next(x for x in bs if x['case']==s['case'] and x['method']=='fir_checked')
    assert s['task_spec']==original['task_spec'] and s['truth']==original['truth']
    assert len(s['admissions'])==2 and s['admissions'][0]==original['admissions'][0]
    if not s['revision_accepted']:
        assert s['pieces']==fallback['pieces']
        assert s['admissions'][1]['target_m']=='0' and s['admissions'][1]['outcome']=='optimizer_rejected'
        assert all(not r['full_task_pass'] for r in rows if r['method']==s['method'] and r['case']==s['case'])
    else:
        assert s['planned_reference_arrival_exact']=='71/50' and s['revision_execution_exact']=='13/25'
        assert s['reference_deadline_feasible']==(s['case']=='return_generous')
        assert all(r['full_task_pass']==(s['case']=='return_generous') for r in rows if r['method']==s['method'] and r['case']==s['case'])
# Figure provenance: top panels one stated plant; bottom panels six plant cases.
figure=read(B/'figure-runtime.json')
assert len(figure['files'])==4
for path,digest in figure['files'].items():assert sha(Path(path))==digest
assert all('__r100__w00__dt500us.csv.gz' in path and 'return_generous' in path for path in figure['files'])
selected=[r for r in rows if r['method']=='smooth_n90_cap10mm' and r['case']=='return_generous' and r['sample_step_s']==.0005]
violators=[{'rate':r['rate'],'disturbance':r['disturbance'],'sampled_actual_extra_travel_m':r['suffix_until_horizon_extra_forward_excursion_m']} for r in selected if r['suffix_until_horizon_extra_forward_excursion_m']>.01]
assert violators
out={'status':'PASS','manifest_files_checked':checked,'physical_rows':new['rows'],'physical_event_sides_checked':new['events'],'aggregate_values_checked':fields,'max_aggregate_discrepancy':maxdiff,'common_prefix_comparisons_against_three_methods':prefixes,'all_prefixes_identical_in_serialized_values_and_55_digit_independent_replay':True,'retained_failed_requests':True,'original_truth_not_changed_after_rejection':True,'same_return_plan_both_deadlines':True,'generous_accepted_cases':len(selected),'generous_task_passes':sum(r['full_task_pass'] for r in selected),'tight_task_passes':sum(r['full_task_pass'] for r in rows if r['method']=='smooth_n90_cap10mm' and r['case']=='return_tight' and r['sample_step_s']==.0005),'reference_cap_not_actual_cap_witnesses':violators,'figure_input_hashes_verified':True,'row_tolerances':'1e-12 for state/command/reference fields; 1e-11 for physical jerk, command derivative and reference snap. Comparison tolerance, not an integration error bound.','metrics_tolerance':'Every independently recomputed physical metric differs by less than1e-10; figures/ranges/ratios by less than1e-9.','reuse':'Prior critic03 already-replayed baseline rows are reused with their complete frozen evidence; all90 new physical traces are replayed afresh.'}
(HERE/'summary-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
