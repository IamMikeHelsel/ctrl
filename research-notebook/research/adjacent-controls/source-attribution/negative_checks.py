#!/usr/bin/env python3
"""Corrupt disposable result copies and require the acceptance checker to reject them."""
from pathlib import Path
from fractions import Fraction as F
import copy
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
original = json.loads((ROOT/'results.json').read_text())

def drop_stage(r): del r['stages']['duplicate']
def drop_branch(r): del r['stages']['baseline']['branches']['nonpositive_d']
def drop_objective(r): del r['stages']['baseline']['branches']['nonnegative_d']['bounds']['drivetrain']
def drop_range(r): del r['stages']['baseline']['ranges']['drivetrain']
def drop_action(r): del r['stages']['baseline']['actions']['-1']
def alter_endpoint(r):
    bounds = r['stages']['separated']['branches']['nonnegative_d']['bounds']['wheel']['range']
    bounds[1] = str(F(bounds[1])+1)
def alter_dual(r):
    term = r['stages']['separated']['branches']['nonnegative_d']['bounds']['wheel']['upper_dual'][0]
    term['weight'] = str(F(term['weight'])+1)
def empty_accept(r):
    # A false claim of emptiness cannot supply valid Farkas proofs for this
    # nonempty model. It must fail before any universal action claim is accepted.
    for b in r['stages']['separated']['branches'].values():
        b.clear()
        b.update({'constraints': original['stages']['separated']['branches']['nonnegative_d']['constraints'],
                  'feasible': False, 'farkas': []})
    r['stages']['separated']['actions']['-1']['accepted'] = True
def false_action(r): r['stages']['baseline']['actions']['-1/2']['accepted'] = True
def false_held_out(r): r['held_out_checks']['held_out']['compatible_in_scalar_model'] = False
def drop_held_out(r): del r['held_out_checks']['deliberately_inconsistent_held_out']
def false_same_readings(r): r['duplicate_and_trial_sets_equal_baseline'] = False
def wrong_model_hash(r): r['model_sha256'] = '0'*64

CASES = [
    ('drop_stage', drop_stage, 'Stage set incomplete'),
    ('drop_branch', drop_branch, 'Branch set incomplete'),
    ('drop_objective', drop_objective, 'Bound set incomplete'),
    ('drop_range', drop_range, 'Range set incomplete'),
    ('drop_action', drop_action, 'Action set incomplete'),
    ('alter_bound_endpoint', alter_endpoint, 'Bound endpoint not attained'),
    ('alter_dual_weight', alter_dual, 'Invalid upper dual'),
    ('forged_empty_set_acceptance', empty_accept, 'Invalid infeasibility certificate'),
    ('false_action_acceptance', false_action, 'Incorrect action decision'),
    ('false_held_out_compatibility', false_held_out, 'Incorrect held-out compatibility'),
    ('drop_held_out_case', drop_held_out, 'Held-out case set incomplete'),
    ('false_same_readings_claim', false_same_readings, 'Incorrect same-readings claim'),
    ('wrong_model_binding', wrong_model_hash, 'Result/model hash mismatch'),
]

normal = subprocess.run([sys.executable, str(ROOT/'check.py')], capture_output=True, text=True)
assert normal.returncode == 0, normal.stderr
(ROOT/'check.log').write_text(normal.stdout+normal.stderr)
records = []
with tempfile.TemporaryDirectory(prefix='corrupt-results-', dir=ROOT) as tmp:
    for name, mutate, expected in CASES:
        value = copy.deepcopy(original)
        mutate(value)
        path = Path(tmp)/(name+'.json')
        path.write_text(json.dumps(value))
        run = subprocess.run([sys.executable, str(ROOT/'check.py'), '--input', str(path)], capture_output=True, text=True)
        assert run.returncode != 0 and expected in run.stderr, (name, run.returncode, run.stderr)
        records.append({'case': name, 'rejected': True, 'exit_code': run.returncode,
                        'diagnostic': run.stderr.strip().splitlines()[-1]})
optimized = subprocess.run([sys.executable, '-O', str(ROOT/'check.py')], capture_output=True, text=True)
assert optimized.returncode != 0 and 'Run without Python -O' in optimized.stderr
records.append({'case': 'disabled_assertions', 'rejected': True, 'exit_code': optimized.returncode,
                'diagnostic': optimized.stderr.strip().splitlines()[-1]})
report = {'normal_passed': True, 'negative_case_count': len(records), 'all_rejected': True,
          'cases': records, 'sha256': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
            for name in ('model.json', 'experiment.py', 'results.json', 'check.py', 'negative_checks.py')}}
(ROOT/'negative-checks.json').write_text(json.dumps(report, indent=2)+'\n')
print(f'PASS: normal result accepted; {len(records)} corrupted/unsafe checker invocations rejected.')
print('The predeclared model and saved producer result were not modified.')
