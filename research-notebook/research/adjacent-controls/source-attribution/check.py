#!/usr/bin/env python3
"""Check this fixed demo's complete certificates without rerunning LP search."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
MODEL_SHA256 = '9f2ff239496551e75477405e91048a69d91eb3759d949a94501e3ebc13d9b867'
STAGES = {'baseline', 'duplicate', 'trial', 'separated'}
SIGNS = {'nonnegative_d', 'nonpositive_d'}
OBJECTIVES = {'wheel': (F(1), F(0), F(0)), 'drivetrain': (F(0), F(1), F(0)),
              'baseline_response': (F(1), F(1), F(0)),
              'held_out_prediction': (F(1), F(0), F(1, 2))}
HELD_OUT = {'held_out', 'deliberately_inconsistent_held_out'}

def dot(a, b):
    assert len(a) == len(b), 'Vector length mismatch'
    return sum((x*y for x, y in zip(a, b)), F(0))

def weighted(c, terms):
    a = [F(0)]*3
    b = F(0)
    for term in terms:
        assert set(term) == {'constraint', 'weight'}
        index = term['constraint']
        assert type(index) is int and 0 <= index < len(c), 'Bad constraint index'
        weight = F(term['weight'])
        assert weight >= 0, 'Negative certificate weight'
        row = c[index]
        a = [v+weight*z for v, z in zip(a, row[0])]
        b += weight*row[1]
    return tuple(a), b

def expected(m, stage, sign):
    wl, wu = map(F, m['prior']['w'])
    dl, du = map(F, m['prior']['d'])
    c = {((F(1), F(0), F(0)), wu), ((F(-1), F(0), F(0)), -wl),
         ((F(0), F(1), F(0)), du), ((F(0), F(-1), F(0)), -dl)}
    lo, hi = map(F, m['prior']['lambda'])
    if sign == 'nonnegative_d':
        c.update({((F(0), F(-1), F(0)), F(0)),
                  ((F(0), lo, F(-1)), F(0)), ((F(0), -hi, F(1)), F(0))})
    else:
        assert sign == 'nonpositive_d'
        c.update({((F(0), F(1), F(0)), F(0)),
                  ((F(0), hi, F(-1)), F(0)), ((F(0), -lo, F(1)), F(0))})
    readings = ['baseline'] + (['trial'] if stage in ('trial', 'separated') else []) + (['separating'] if stage == 'separated' else [])
    for name in readings:
        s = m[name]
        a = tuple(map(F, s['row']))
        y = F(s['value'])-F(s.get('wheel_offset', '0'))
        e = F(s['error_bound'])
        c.update({(a, y+e), (tuple(-z for z in a), -y+e)})
    return c

def valid_witness(m, c, raw):
    witness = tuple(map(F, raw))
    assert len(witness) == 3
    assert all(dot(a, witness) <= rhs for a, rhs in c), 'Infeasible witness'
    w, d, q = witness
    lo, hi = map(F, m['prior']['lambda'])
    assert (d == 0 and q == 0) or (d != 0 and lo <= q/d <= hi), 'Invalid shared leakage'
    return witness

def verify(r, m):
    assert r['model_sha256'] == MODEL_SHA256, 'Result/model hash mismatch'
    assert r['script_sha256'] == hashlib.sha256((ROOT/'experiment.py').read_bytes()).hexdigest(), 'Producer hash mismatch'
    assert set(r['stages']) == STAGES, 'Stage set incomplete or unexpected'
    assert set(m['actions']) == {'-1/2', '-1'} and len(m['actions']) == 2
    action_keys = set(m['actions'])
    bound_count = empty_count = action_count = 0
    all_constraints = {}
    for stage, s in r['stages'].items():
        assert set(s['branches']) == SIGNS, 'Branch set incomplete or unexpected'
        assert set(s['ranges']) == set(OBJECTIVES), 'Range set incomplete or unexpected'
        assert set(s['actions']) == action_keys, 'Action set incomplete or unexpected'
        feasible = []
        for sign, b in s['branches'].items():
            assert type(b['feasible']) is bool, 'Feasibility flag must be Boolean'
            c = [(tuple(map(F, z['a'])), F(z['b'])) for z in b['constraints']]
            assert set(c) == expected(m, stage, sign), 'Constraint set does not match model'
            all_constraints[stage, sign] = c
            if not b['feasible']:
                assert set(b) == {'constraints', 'feasible', 'farkas'}, 'Unexpected infeasible-branch fields'
                assert weighted(c, b['farkas']) == ((F(0), F(0), F(0)), F(-1)), 'Invalid infeasibility certificate'
                empty_count += 1
                continue
            assert set(b) == {'constraints', 'feasible', 'vertices', 'bounds'}, 'Unexpected feasible-branch fields'
            assert set(b['bounds']) == set(OBJECTIVES), 'Bound set incomplete or unexpected'
            assert b['vertices'], 'Missing vertex witnesses'
            for vertex in b['vertices']:
                valid_witness(m, c, vertex)
            feasible.append(b)
            for name, cert in b['bounds'].items():
                objective = OBJECTIVES[name]
                lo, hi = map(F, cert['range'])
                assert lo <= hi
                for side, val in [('lower', lo), ('upper', hi)]:
                    witness = valid_witness(m, c, cert[side+'_witness'])
                    assert dot(objective, witness) == val, 'Bound endpoint not attained by witness'
                assert weighted(c, cert['upper_dual']) == (objective, hi), 'Invalid upper dual'
                assert weighted(c, cert['lower_dual_for_negative_objective']) == (tuple(-z for z in objective), -lo), 'Invalid lower dual'
                bound_count += 2
        assert feasible, 'Never certify an action from an empty model set'
        for name in OBJECTIVES:
            exact_range = [min(F(b['bounds'][name]['range'][0]) for b in feasible),
                           max(F(b['bounds'][name]['range'][1]) for b in feasible)]
            assert list(map(F, s['ranges'][name])) == exact_range, 'Incorrect global range'
        for ctext, a in s['actions'].items():
            c = F(ctext)
            wr = [F(x)+c for x in s['ranges']['wheel']]
            sr = [F(x)+c for x in s['ranges']['baseline_response']]
            assert list(map(F, a['corrected_wheel_range'])) == wr, 'Incorrect corrected range'
            assert F(a['worst_abs_wheel']) == max(map(abs, wr)), 'Incorrect wheel bound'
            assert F(a['worst_abs_mixed_response_for_all_rho_0_1']) == max(map(abs, wr+sr)), 'Incorrect mixed bound'
            assert type(a['accepted']) is bool
            assert a['accepted'] == (max(map(abs, wr)) <= F(m['acceptance']['wheel_component_limit']) and max(map(abs, wr+sr)) <= F(m['acceptance']['mixed_response_limit'])), 'Incorrect action decision'
            action_count += 1
    same = all(set(all_constraints[stage, sign]) == set(all_constraints['baseline', sign])
               for stage in ('duplicate', 'trial') for sign in SIGNS)
    assert same and r['duplicate_and_trial_sets_equal_baseline'] is True, 'Incorrect same-readings claim'
    witnesses = r['indistinguishable_baseline_and_trial_witnesses_w_d_q']
    assert len(witnesses) == 2
    wx = [valid_witness(m, all_constraints['trial', 'nonnegative_d'], x) for x in witnesses]
    assert wx[0][0] != wx[1][0] and wx[0][1] != wx[1][1]
    assert dot(OBJECTIVES['baseline_response'], wx[0]) == dot(OBJECTIVES['baseline_response'], wx[1]), 'Witnesses distinguishable by common row'
    assert set(r['held_out_checks']) == HELD_OUT, 'Held-out case set incomplete or unexpected'
    # Only one nonempty convex branch: interval overlap is an existence test here.
    assert {sign for sign in SIGNS if r['stages']['separated']['branches'][sign]['feasible']} == {'nonnegative_d'}
    prediction = list(map(F, r['stages']['separated']['ranges']['held_out_prediction']))
    for name, h in r['held_out_checks'].items():
        spec = m[name]
        obs = [F(spec['value'])-F(spec['error_bound']), F(spec['value'])+F(spec['error_bound'])]
        assert list(map(F, h['prediction'])) == prediction, 'Incorrect held-out prediction'
        assert list(map(F, h['observed_interval'])) == obs, 'Incorrect held-out observation interval'
        compatible = max(prediction[0], obs[0]) <= min(prediction[1], obs[1])
        assert type(h['compatible_in_scalar_model']) is bool and h['compatible_in_scalar_model'] == compatible, 'Incorrect held-out compatibility'
        assert h['used_for_identification'] is False and spec['use_for_identification'] is False
    assert r['held_out_checks']['held_out']['compatible_in_scalar_model'] is True
    assert r['held_out_checks']['deliberately_inconsistent_held_out']['compatible_in_scalar_model'] is False
    rejected = r['rejected_action_witness']
    x = valid_witness(m, all_constraints['separated', 'nonnegative_d'], rejected['w_d_q'])
    action = F(rejected['action'])
    assert action == -1 and F(rejected['wheel_residual']) == x[0]+action
    assert abs(x[0]+action) > F(m['acceptance']['wheel_component_limit']), 'Rejected witness does not violate limit'
    assert (bound_count, empty_count, action_count) == (56, 1, 8), 'Unexpected checked certificate counts'
    return bound_count, empty_count, action_count

def main():
    if not __debug__:
        raise RuntimeError('Run without Python -O: assertions are the checker conditions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=ROOT/'results.json')
    args = parser.parse_args()
    assert hashlib.sha256((ROOT/'model.json').read_bytes()).hexdigest() == MODEL_SHA256, 'Predeclared model changed'
    m = json.loads((ROOT/'model.json').read_text())
    counts = verify(json.loads(args.input.read_text()), m)
    print(f'PASS: {counts[0]} exact bound certificates, {counts[1]} infeasibility certificate, {counts[2]} action evaluations; all stages nonempty.')
    print('Complete stage/branch/objective/action coverage and held-out summaries checked.')
    print('This is a Python/Fraction certificate check, not Lean/kernel verification or physical validation.')

if __name__ == '__main__':
    main()
