#!/usr/bin/env python3
"""Exact rational bounded attribution. No packages, grid search, or Lean claim."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent
MODEL_PATH = ROOT / 'model.json'
MODEL = json.loads(MODEL_PATH.read_text())

def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))

def solve(a, b):
    """Exact square Gaussian elimination; None means singular."""
    n = len(b)
    m = [list(map(F, row)) + [F(rhs)] for row, rhs in zip(a, b)]
    for k in range(n):
        p = next((j for j in range(k, n) if m[j][k]), None)
        if p is None:
            return None
        m[k], m[p] = m[p], m[k]
        pivot = m[k][k]
        m[k] = [x/pivot for x in m[k]]
        for j in range(n):
            if j != k:
                v = m[j][k]
                m[j] = [x-v*y for x, y in zip(m[j], m[k])]
    return tuple(row[-1] for row in m)

def con(label, row, rhs):
    return {'label': label, 'a': tuple(map(F, row)), 'b': F(rhs)}

def observed(name):
    spec = MODEL[name]
    a = tuple(map(F, spec['row']))
    y = F(spec['value']) - F(spec.get('wheel_offset', '0'))
    e = F(spec['error_bound'])
    return [con(name+'_upper', a, y+e),
            con(name+'_lower', tuple(-x for x in a), -y+e)]

def constraints(stage, sign):
    c = [con('w_upper', (1, 0, 0), 2), con('w_lower', (-1, 0, 0), 2),
         con('d_upper', (0, 1, 0), 2), con('d_lower', (0, -1, 0), 2)]
    lo, hi = map(F, MODEL['prior']['lambda'])
    if sign == 'nonnegative_d':
        c += [con('d_nonnegative', (0, -1, 0), 0),
              con('leak_lower', (0, lo, -1), 0),
              con('leak_upper', (0, -hi, 1), 0)]
    else:
        c += [con('d_nonpositive', (0, 1, 0), 0),
              con('leak_lower', (0, hi, -1), 0),
              con('leak_upper', (0, -lo, 1), 0)]
    c += observed('baseline')
    if stage in ('duplicate', 'trial', 'separated'):
        c += [con('duplicate_'+x['label'], x['a'], x['b']) for x in observed('baseline')]
    if stage in ('trial', 'separated'):
        c += observed('trial')
    if stage == 'separated':
        c += observed('separating')
    return c

def unique_constraints(c):
    return sorted(set((x['a'], x['b']) for x in c))

def vertices(c):
    out = set()
    for ids in combinations(range(len(c)), 3):
        x = solve([c[i]['a'] for i in ids], [c[i]['b'] for i in ids])
        if x is not None and all(dot(t['a'], x) <= t['b'] for t in c):
            out.add(x)
    return sorted(out)

def dual(c, objective, optimum, witness):
    active = [i for i, t in enumerate(c) if dot(t['a'], witness) == t['b']]
    for ids in combinations(active, 3):
        weights = solve([[c[i]['a'][j] for i in ids] for j in range(3)], objective)
        if weights is not None and min(weights) >= 0 and dot(weights, [c[i]['b'] for i in ids]) == optimum:
            assert all(sum((weights[k]*c[i]['a'][j] for k, i in enumerate(ids)), F(0)) == objective[j] for j in range(3))
            return [{'constraint': i, 'weight': w} for i, w in zip(ids, weights) if w]
    raise AssertionError('No exact upper-bound certificate')

def farkas(c):
    """Find nonnegative weights with sum weight*a=0, sum weight*b=-1."""
    for ids in combinations(range(len(c)), 4):
        cols = [c[i]['a']+(c[i]['b'],) for i in ids]
        weights = solve([[col[j] for col in cols] for j in range(4)], (0, 0, 0, -1))
        if weights is not None and min(weights) >= 0:
            assert all(sum((weights[k]*c[i]['a'][j] for k, i in enumerate(ids)), F(0)) == 0 for j in range(3))
            assert dot(weights, [c[i]['b'] for i in ids]) == -1
            return [{'constraint': i, 'weight': w} for i, w in zip(ids, weights) if w]
    raise AssertionError('No exact infeasibility certificate')

def bound(c, v, objective):
    lo = min(dot(objective, x) for x in v)
    hi = max(dot(objective, x) for x in v)
    low_x = next(x for x in v if dot(objective, x) == lo)
    high_x = next(x for x in v if dot(objective, x) == hi)
    return {'range': [lo, hi], 'lower_witness': low_x, 'upper_witness': high_x,
            'lower_dual_for_negative_objective': dual(c, tuple(-z for z in objective), -lo, low_x),
            'upper_dual': dual(c, objective, hi, high_x)}

OBJECTIVES = {'wheel': (F(1), F(0), F(0)), 'drivetrain': (F(0), F(1), F(0)),
              'baseline_response': (F(1), F(1), F(0)),
              'held_out_prediction': (F(1), F(0), F(1, 2))}

def branch(stage, sign):
    c = constraints(stage, sign)
    v = vertices(c)
    if not v:
        return {'constraints': c, 'feasible': False, 'farkas': farkas(c)}
    # Each lifted vertex corresponds to a genuine shared leakage value.
    for w, d, q in v:
        assert (d == 0 and q == 0) or (d != 0 and F(1, 5) <= q/d <= F(3, 10))
    return {'constraints': c, 'feasible': True, 'vertices': v,
            'bounds': {name: bound(c, v, obj) for name, obj in OBJECTIVES.items()}}

def stage_result(stage):
    branches = {s: branch(stage, s) for s in ('nonnegative_d', 'nonpositive_d')}
    feasible = [b for b in branches.values() if b['feasible']]
    assert feasible, 'Empty feasible set: block action certification and reject model/data contract'
    ranges = {name: [min(b['bounds'][name]['range'][0] for b in feasible),
                     max(b['bounds'][name]['range'][1] for b in feasible)] for name in OBJECTIVES}
    actions = {}
    for ctext in MODEL['actions']:
        c = F(ctext)
        wr = [z+c for z in ranges['wheel']]
        sr = [z+c for z in ranges['baseline_response']]
        wheel = max(map(abs, wr))
        # For every fixed state, |w+c+rho*d| is convex in rho. Endpoints suffice.
        mixed = max(map(abs, wr+sr))
        actions[ctext] = {'corrected_wheel_range': wr, 'worst_abs_wheel': wheel,
                          'worst_abs_mixed_response_for_all_rho_0_1': mixed,
                          'accepted': wheel <= F(MODEL['acceptance']['wheel_component_limit']) and mixed <= F(MODEL['acceptance']['mixed_response_limit'])}
    return {'branches': branches, 'ranges': ranges, 'actions': actions}

def encode(x):
    if isinstance(x, F): return str(x)
    if isinstance(x, dict): return {k: encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)): return [encode(v) for v in x]
    return x

def main():
    start = time.monotonic()
    stages = {s: stage_result(s) for s in ('baseline', 'duplicate', 'trial', 'separated')}
    same = all(unique_constraints(constraints(s, sign)) == unique_constraints(constraints('baseline', sign))
               for s, sign in product(('duplicate', 'trial'), ('nonnegative_d', 'nonpositive_d')))
    assert same
    truth = tuple(F(MODEL['illustrative_truth_not_given_to_estimator'][k]) for k in ('w', 'd', 'lambda'))
    tx = (truth[0], truth[1], truth[1]*truth[2])
    assert all(dot(c['a'], tx) <= c['b'] for c in constraints('separated', 'nonnegative_d'))
    held = stages['separated']['ranges']['held_out_prediction']
    held_checks = {}
    for name in ('held_out', 'deliberately_inconsistent_held_out'):
        spec = MODEL[name]
        obs = [F(spec['value'])-F(spec['error_bound']), F(spec['value'])+F(spec['error_bound'])]
        compatible = max(held[0], obs[0]) <= min(held[1], obs[1])
        held_checks[name] = {'prediction': held, 'observed_interval': obs,
                             'compatible_in_scalar_model': compatible,
                             'used_for_identification': False}
    assert held_checks['held_out']['compatible_in_scalar_model']
    assert not held_checks['deliberately_inconsistent_held_out']['compatible_in_scalar_model']
    assert stages['separated']['actions']['-1/2']['accepted']
    assert not stages['separated']['actions']['-1']['accepted']
    indistinguishable = [(F(1), F(0), F(0)), (F(0), F(1), F(1, 4))]
    assert all(all(dot(c['a'], x) <= c['b'] for c in constraints('trial', 'nonnegative_d')) for x in indistinguishable)
    result = {'status': 'Exact rational computation with checked linear bound certificates; not Lean verified',
              'model_sha256': hashlib.sha256(MODEL_PATH.read_bytes()).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'duplicate_and_trial_sets_equal_baseline': same,
              'indistinguishable_baseline_and_trial_witnesses_w_d_q': indistinguishable,
              'stages': stages, 'held_out_checks': held_checks,
              'rejected_action_witness': {'w_d_q': tx, 'action': F(-1), 'wheel_residual': tx[0]-1},
              'runtime_seconds': time.monotonic()-start}
    (ROOT/'results.json').write_text(json.dumps(encode(result), indent=2)+'\n')
    for name, s in stages.items():
        print(name, 'wheel=', s['ranges']['wheel'], 'actions=', s['actions'])
    print('Held out:', held_checks)
    print('Seconds:', result['runtime_seconds'])

if __name__ == '__main__':
    main()
