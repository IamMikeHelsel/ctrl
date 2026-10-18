"""Summarize every declared solver case; no tuning or new plant simulation."""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import csv, gzip, hashlib, json

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'builder-03'
METRICS = [
    'suffix_until_horizon_jerk_energy_m2_s5',
    'suffix_until_horizon_extra_forward_excursion_m',
    'suffix_until_horizon_path_length_m',
    'suffix_until_horizon_command_total_TV_m_s2',
    'suffix_until_horizon_actual_jerk_peak_m_s3',
    'suffix_until_horizon_overshoot_beyond_goal_m',
    'suffix_until_matched_arrival_jerk_energy_m2_s5',
]
def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

def main():
    rows = json.loads((HERE/'metrics.json').read_text())['rows']
    baseline = json.loads((BASE/'metrics.json').read_text())['rows']
    groups = []
    for method in sorted({r['method'] for r in rows + baseline}):
        for case in ['return_generous', 'return_tight']:
            selected = [r for r in rows + baseline if r['method'] == method
                        and r['case'] == case and r['sample_step_s'] == .0005]
            if not selected:
                continue
            groups.append({'method':method, 'case':case, 'cases':len(selected),
                'accepted_requests':sum(r['revision_accepted'] for r in selected),
                'full_task_passes':sum(r['full_task_pass'] for r in selected),
                'ranges':{k:[min(r[k] for r in selected), max(r[k] for r in selected)]
                          for k in METRICS}})
    paired=[]
    for method in ['fir_checked', 'native_fast', 'native_matched']:
        pairs=[]
        for r in rows:
            if r['method']!='smooth_n90_cap10mm' or r['case']!='return_generous' or r['sample_step_s']!=.0005:
                continue
            b=next(b for b in baseline if b['method']==method and b['case']==r['case']
                   and b['sample_step_s']==r['sample_step_s'] and b['rate']==r['rate']
                   and b['disturbance']==r['disturbance'])
            pairs.append({'rate':r['rate'],'disturbance':r['disturbance'],
                          'ratios':{k:r[k]/b[k] for k in METRICS if b[k]!=0}})
        paired.append({'baseline':method,'pairs':pairs})
    grid=[]
    for method in sorted({r['method'] for r in rows if r['grid_N']==90}):
        differences={k:0. for k in METRICS};same=True
        for r in [r for r in rows if r['method']==method and r['sample_step_s']==.0005]:
            b=next(b for b in rows if b['method']==method and b['case']==r['case']
                   and b['sample_step_s']==.001 and b['rate']==r['rate'] and b['disturbance']==r['disturbance'])
            same &= b['full_task_pass']==r['full_task_pass']
            for k in METRICS: differences[k]=max(differences[k],abs(r[k]-b[k]))
        grid.append({'method':method,'task_decisions_unchanged':same,'maximum_absolute_metric_differences':differences})
    result={'created_utc':datetime.now(timezone.utc).isoformat(),
            'status':'root numerical summary; independent review required',
            'scope':'Six plants per group at output step .0005s; no all-time physical claim.',
            'solver_cases':json.loads((HERE/'solver-summary.json').read_text())['cases'],
            'groups':groups,'paired_candidate_ratios':paired,'output_grid_checks':grid,
            'reference_grid_refinement':'N180 produced no accepted candidate; no convergence claim.'}
    write('analysis-summary.json',result)
    table=['method,task,accepted,full_task_passes,jerk_integral_min,jerk_integral_max,excursion_min_mm,excursion_max_mm,peak_jerk_min,peak_jerk_max']
    for g in groups:
        r=g['ranges'];e=r[METRICS[0]];x=r[METRICS[1]];j=r[METRICS[4]]
        table.append(','.join(map(str,[g['method'],g['case'],g['accepted_requests'],g['full_task_passes'],*e,1000*x[0],1000*x[1],*j])))
    (HERE/'comparison-table.csv').write_text('\n'.join(table)+'\n')
    # Final derivative/cap bounds come from exact stored rational controls.
    candidate=json.loads((HERE/'n90_cap10mm.json').read_text())
    write('candidate-summary.json',{
        'reference_jerk_integral_m2_s5':float(F(candidate['corrected_reference_jerk_integral_SI'])),
        'exact_reference_jerk_integral_m2_s5':candidate['corrected_reference_jerk_integral_SI'],
        'exact_reference_bounds':{k:v for k,v in candidate['validation'].items() if k!='controls'},
        'last_three_jerk_corrections_m_s3':[float(F(x)) for x in candidate['last_three_corrections']],
        'max_solver_constraint_violation_mm_units':candidate['max_solver_constraint_violation_mm_units'],
        'max_reference_snap_m_s4':float(F(candidate['validation']['bernstein_absolute_bounds']['snap']))})
    print(json.dumps({'groups':len(groups),'grid_task_decisions_unchanged':all(g['task_decisions_unchanged'] for g in grid)},indent=2))

if __name__=='__main__':main()
