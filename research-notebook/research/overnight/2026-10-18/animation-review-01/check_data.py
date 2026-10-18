"""Independent numerical/display audit; imports no builder or animation code."""
from pathlib import Path
from decimal import Decimal, getcontext
from fractions import Fraction
import csv, gzip, hashlib, json

getcontext().prec = 60
HERE = Path(__file__).resolve().parent
WORK = HERE.parents[3]
POD = WORK / 'research/overnight/2026-10-18/robot-motion'
ANIM = WORK / 'publication/robot-motion/execution-contract-animation'
D = Decimal
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def decq(q): return D(q.numerator) / D(q.denominator)
def verify_manifest(path, expected):
    assert sha(path) == expected, path
    entries = json.loads(path.read_text())['files']
    for relative, item in entries.items():
        expected_hash = item if isinstance(item, str) else item['sha256']
        assert sha(path.parent / relative) == expected_hash, relative
    return len(entries)

gates = {
    ANIM / 'artifact-sha256.json': 'b5a1f043f8814785069da6a7fe4cfe7970b7f16e4cede48554c971a2c676e759',
    POD / 'builder-03/artifact-sha256.json': 'abfc9ca6da02e5cbec77b4019e8f356c80d612f65bea3fcb3e7b227ec1cf6d58',
    POD / 'critic-03/artifact-sha256.json': '2b3cc05bf3e9374bb21478c486424afca21b5d67b76e0bd9551747a9ed5b3660',
    POD / 'smooth-baseline-01/artifact-sha256-final.json': '25d2b152cfc0890bdbef79870560474a291f4bdf64c9076ca0e034eb7fd3f26f',
    POD / 'smooth-review-01/artifact-sha256.json': 'cf71b8400b5a301666587e7787ca1aedca8ec219d4cfb116ac24aee48faf7c04',
}
counts = {str(p.relative_to(WORK)): verify_manifest(p, h) for p, h in gates.items()}
animation = json.loads((ANIM / 'data.json').read_text())
result = {'manifest_counts': counts, 'methods': [], 'source_hashes': {}, 'precision_decimal_digits': 60}
prefixes = []
for item in animation['methods']:
    method = item['method']
    smooth = method.startswith('smooth')
    folder = POD / ('smooth-baseline-01' if smooth else 'builder-03')
    review = POD / ('smooth-review-01' if smooth else 'critic-03')
    stem = f'return_generous__{method}__r100__w00__dt500us'
    source = folder / 'traces' / (stem + '.csv.gz')
    result['source_hashes'][str(source.relative_to(WORK))] = sha(source)
    with gzip.open(source, 'rt') as f:
        raw = list(csv.DictReader(f))
    rows = [{**{k: D(v) for k, v in r.items() if k not in ['time_exact', 'side', 'labels']},
             't': Fraction(r['time_exact']), 'side': r['side']} for r in raw]
    assert len(rows) == len(item['samples'])
    assert all(s['t'] == float(r['t']) and s['x_mm'] == 1000 * float(r['x'])
               for s, r in zip(item['samples'], rows))
    # Repeated event times must have identical physical position for np.interp.
    duplicate_times = 0
    for a, b in zip(rows, rows[1:]):
        assert a['t'] <= b['t']
        if a['t'] == b['t']:
            duplicate_times += 1
            assert all(a[k] == b[k] for k in ['x', 'v', 'a'])
    prefix = [(r['t'], r['side'], r['x'], r['v'], r['a']) for r in rows
              if r['t'] < Fraction(13, 25) or (r['t'] == Fraction(13, 25) and r['side'] == 'left')]
    prefixes.append(prefix)
    suffix = [r for r in rows if Fraction(13,25) <= r['t'] <= Fraction(5,2)]
    revision = next(r for r in rows if r['t'] == Fraction(13,25) and r['side'] == 'left')
    # Every continuous piece ends with its left sample and resumes with its right.
    # Equal-time sides contribute zero area, so the discontinuity is not bridged.
    integral = sum((a['actual_jerk']**2 + b['actual_jerk']**2) * decq(b['t']-a['t']) / 2
                   for a,b in zip(suffix, suffix[1:]))
    peak = max(abs(r['actual_jerk']) for r in suffix)
    excursion = max(D(0), max(r['x'] for r in suffix) - revision['x'])
    path = sum((abs(a['v']) + abs(b['v'])) * decq(b['t']-a['t']) / 2
               for a,b in zip(suffix,suffix[1:]))
    measured = {'jerk_integral': integral, 'peak_jerk': peak, 'extra_travel_mm': excursion*1000}
    saved = next(r for r in json.loads((folder/'metrics.json').read_text())['rows']
                 if r['method']==method and r['case']=='return_generous' and r['rate']==100
                 and r['disturbance']==0 and r['sample_step_s']==.0005)
    independent = next(r for r in json.loads((review/'physical-review.json').read_text())['cases']
                       if r['case_id']==stem)
    original_keys = {'jerk_integral':'suffix_until_horizon_jerk_energy_m2_s5',
                     'peak_jerk':'suffix_until_horizon_actual_jerk_peak_m_s3',
                     'extra_travel_mm':'suffix_until_horizon_extra_forward_excursion_m'}
    differences = {}
    for key, value in measured.items():
        factor = 1000 if key=='extra_travel_mm' else 1
        differences[key] = {'animation':float(abs(value-D(str(item[key])))),
                            'original_metrics':float(abs(value-D(str(saved[original_keys[key]]))*factor)),
                            'independent_replay':float(abs(value-D(str(independent['metrics'][original_keys[key]]))*factor))}
        assert max(differences[key].values()) < 4e-12
        assert f'{float(value):.2f}' == f'{item[key]:.2f}'
    terminal = [r for r in rows if r['t'] >= Fraction(17,10)]
    terminal_peaks = {k:max(abs(r[k]) for r in terminal) for k in ['x','v','a']}
    assert all(terminal_peaks[k] <= bound for k,bound in [('x',D('.0002')),('v',D('.001')),('a',D('.02'))])
    assert max(abs(r['x']-r['q']) for r in rows) <= D('.0002')
    assert next(r['x'] for r in rows if r['t']==Fraction(1,2)) >= D('.001')
    assert saved['revision_accepted'] and saved['full_task_pass']
    assert independent['metrics']['full_task_pass']
    assert all(D(str(p)) <= D(str(b))+D('1e-10') for p,b in zip(independent['reference_critical_peaks'],[.1,.5,7.5]))
    # The paper frame displays rounded time0.69. Check the entire rounding bin,
    # with neighboring samples included, rather than infer velocity from dots.
    frame_bin = [r for r in rows if Fraction(6845,10000) <= r['t'] <= Fraction(6955,10000)]
    assert frame_bin and min(r['v'] for r in frame_bin) > 0
    result['methods'].append({'method':method,'rows':len(rows),'duplicate_times':duplicate_times,
      'recomputed':{k:str(v) for k,v in measured.items()},'display':{k:f'{float(v):.2f}' for k,v in measured.items()},
      'difference':differences,'terminal_peaks':{k:str(v) for k,v in terminal_peaks.items()},
      'sampled_task_pass':True,'forward_velocity_min_at_paper_frame_m_s':str(min(r['v'] for r in frame_bin)),
      'forward_velocity_max_at_paper_frame_m_s':str(max(r['v'] for r in frame_bin)),
      'suffix_total_path_mm':str(path*1000),'frame_range_s':['0.6845','0.6955']})
assert all(p == prefixes[0] for p in prefixes[1:])
result['all_samples_match'] = True
result['identical_physical_prefix'] = True
result['all_task_passes_supported'] = True
result['paper_frame_all_forward'] = True
result['status'] = 'PASS'
(HERE/'data-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
