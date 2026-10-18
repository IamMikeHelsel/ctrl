#!/usr/bin/env python3
"""Fresh target build, all-public-theorem axiom audit, kernel replay and false bound."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[5]
BASE = WORK / 'lean-controls'
MODULE = 'CausalAdmission'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    env = os.environ.copy()
    env['ELAN_HOME'] = str(WORK / '.tools/elan')
    lake = str(WORK / '.tools/elan/bin/lake')
    def query(*args):
        return subprocess.check_output([lake, 'env', *args], cwd=BASE, env=env, text=True).strip()
    lean = query('which', 'lean')
    checker = str(Path(lean).with_name('leanchecker'))
    dep = ':'.join(str((BASE / p).resolve()) if not Path(p).is_absolute() else p
                   for p in query('printenv', 'LEAN_PATH').split(':'))
    source_path = HERE / (MODULE + '.lean')
    source = source_path.read_text()
    stripped = re.sub(r'/-.*?-/|--[^\n]*', '', source, flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', stripped)
    namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
    names = [namespace + '.' + name for name in re.findall(r'^(?:theorem|lemma) (\w+)', source, re.M)]
    assert names and len(names) == len(set(names))
    mathlib = BASE / '.lake/packages/mathlib'
    logs = HERE / 'verification-logs'
    logs.mkdir(exist_ok=True)
    (HERE / 'build').mkdir(exist_ok=True)
    report = {
        'passed': False,
        'scope': 'One target copied and compiled fresh. Pinned Lean/Mathlib dependency artifacts reused. All public target theorems audited. Separate leanchecker replay.',
        'toolchain': query('lean', '--version'),
        'lean_executable': lean,
        'leanchecker_executable': checker,
        'lean_toolchain_file': (BASE / 'lean-toolchain').read_text().strip(),
        'mathlib_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib, text=True).strip(),
        'mathlib_status': subprocess.check_output(['git', 'status', '--porcelain'], cwd=mathlib, text=True),
        'source_sha256': {MODULE: sha(source_path)},
        'source_paths': {MODULE: str(source_path.relative_to(WORK))},
        'verifier_sha256': sha(Path(__file__)),
        'lake_manifest_sha256': sha(BASE / 'lake-manifest.json'),
        'audited_statement_names': names,
        'steps': [],
        'axioms': {},
    }
    def save():
        (HERE / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    def run(label, args, cwd, renv, negative=False):
        start = time.monotonic()
        logfile = logs / (label + '.log')
        with logfile.open('w') as out:
            result = subprocess.run(args, cwd=cwd, env=renv, stdout=out,
                                    stderr=subprocess.STDOUT, timeout=600)
        ok = result.returncode != 0 if negative else result.returncode == 0
        report['steps'].append({'label': label, 'exit_code': result.returncode,
            'passed': ok, 'expected': 'rejection' if negative else 'success',
            'seconds': time.monotonic()-start, 'log_sha256': sha(logfile)})
        save()
        print(label, result.returncode, flush=True)
        assert ok, label
    with tempfile.TemporaryDirectory(prefix='fresh-', dir=HERE / 'build') as tmp:
        root = Path(tmp)
        renv = env.copy()
        renv['LEAN_PATH'] = str(root) + ':' + dep
        renv['PATH'] = str(Path(lean).parent) + os.pathsep + env.get('PATH', '')
        shutil.copy2(source_path, root / source_path.name)
        run('build-' + MODULE, [lean, '--root=' + str(root), '-o',
            str(root / (MODULE + '.olean')), str(root / source_path.name)], root, renv)
        (root / 'Audit.lean').write_text('import ' + MODULE + '\n' +
            '\n'.join('#print axioms ' + name for name in names) + '\n')
        run('axiom-audit', [lean, str(root / 'Audit.lean')], root, renv)
        for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",
                                   (logs / 'axiom-audit.log').read_text()):
            axioms = {x.strip() for x in raw.split(',') if x.strip()}
            assert axioms <= ALLOWED, (name, axioms)
            report['axioms'][name] = sorted(axioms)
        assert set(report['axioms']) == set(names)
        run('kernel-' + MODULE, [checker, MODULE, '-v'], root, renv)
        old = '    deadline a0 J S ≤ T := by'
        assert source.count(old) == 1
        false_source = source.replace(old, '    deadline a0 J S + J / S ≤ T := by')
        (root / 'FalseDeadline.lean').write_text(false_source)
        run('reject-false-extra-delay', [lean, str(root / 'FalseDeadline.lean')], root, renv, negative=True)
        reject_log = (logs / 'reject-false-extra-delay.log').read_text()
        assert 'linarith failed' in reject_log and 'error: unknown' not in reject_log
        report['negative_control_reason'] = (
            'The false mutation adds J/S to the necessary deadline. The accepted general admissible '
            'attainer reaches zero at a0/J+2J/S. For a0=5/2,J=10,S=400 the false claim demands '
            'T>=13/40, while the accepted trajectory reaches zero at T=3/10.')
        witness = '''import CausalAdmission
open CausalAdmission
example : IsAdmissible (5/2) 10 400 (3/10)
    (leastAccel (5/2) 10 400) (leastJerk 10 400) (leastSnap 10 400) :=
  least_isAdmissible _ _ (by norm_num) (by norm_num)
example : leastAccel (5/2) 10 400 (3/10) = 0 := by
  rw [← exact_earliest_deadline]
  exact least_reaches_zero (by norm_num) (by norm_num) (by norm_num)
example : ¬ deadline (5/2) 10 400 + 10/400 ≤ (3/10 : ℝ) := by
  norm_num [deadline, rampTime]
'''
        (root / 'MutationWitness.lean').write_text(witness)
        (HERE / 'MutationWitness.lean').write_text(witness)
        run('accepted-counterexample-to-mutation', [lean, str(root / 'MutationWitness.lean')], root, renv)
    report['source_unchanged'] = sha(source_path) == report['source_sha256'][MODULE]
    report['passed'] = report['source_unchanged'] and all(s['passed'] for s in report['steps'])
    save()
    print(json.dumps({'passed': report['passed'], 'audited_public_theorems': len(names)}))

if __name__ == '__main__':
    main()
