"""Independent frozen-source replay. Does not execute or modify builder scripts."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

G = Path(__file__).resolve().parent
B = G.parent / 'builder'
ROOT = G.parents[5]
BASE = ROOT / 'lean-controls'
MANIFEST = 'a283b2848de505c7565eb768e35215d9330f2eedfc015d51876fb29784aaf085'
MODULES = ['CliffordModel', 'ContractionAlgebra', 'CliffordContraction', 'CliffordControls']
NAMESPACES = ['GUClifford', 'GUContraction', 'GUClifford', 'GUClifford']

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory():
    assert digest(B / 'SHA256SUMS') == MANIFEST
    result = {}
    for row in (B / 'SHA256SUMS').read_text().splitlines():
        expected, name = row.split('  ', 1)
        actual = digest(B / name)
        assert actual == expected, name
        result[name] = actual
    assert len(result) == 34
    result['SHA256SUMS'] = digest(B / 'SHA256SUMS')
    return result

before = inventory()
(G / 'hashes-before.json').write_text(json.dumps(before, indent=2) + '\n')
env = os.environ.copy()
env['ELAN_HOME'] = str(ROOT / '.tools/elan')
lake = str(ROOT / '.tools/elan/bin/lake')
lean = subprocess.check_output([lake, 'env', 'which', 'lean'], cwd=BASE, env=env, text=True).strip()
raw_paths = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=BASE, env=env, text=True).strip()
paths = [str((BASE / p).resolve()) for p in raw_paths.split(':')]
env['PATH'] = str(Path(lean).parent) + ':' + env['PATH']
version = subprocess.check_output([lean, '--version'], env=env, text=True).strip()
assert 'version 4.35.0,' in version
revision = next(p['rev'] for p in json.loads((BASE / 'lake-manifest.json').read_text())['packages'] if p['name'] == 'mathlib')
assert revision == '56a005855ea17e0b0958f73ec801ae140b0a1679'
steps = []

def run(label, argv, cwd, succeeds=True):
    started = time.monotonic()
    proc = subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True, timeout=300)
    output = proc.stdout + proc.stderr
    (G / 'logs' / (label + '.log')).write_text(output)
    steps.append({'label': label, 'command': argv, 'exit': proc.returncode,
                  'seconds': round(time.monotonic() - started, 3)})
    print(json.dumps({k: v for k, v in steps[-1].items() if k != 'command'}), flush=True)
    assert (proc.returncode == 0) == succeeds, output[-12000:]
    return output

names = []
for module, namespace in zip(MODULES, NAMESPACES):
    src = B / (module + '.lean')
    text = src.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', text)
    names += [namespace + '.' + name for name in re.findall(r'^theorem\s+([^\s(:]+)', text, re.M)]
    (G / 'replay-sources' / src.name).write_bytes(src.read_bytes())
assert len(names) == len(set(names)) == 52
audit = '\n'.join('import ' + m for m in MODULES) + '\n' + '\n'.join('#print axioms ' + n for n in names) + '\n'
(G / 'replay-sources/Audit.lean').write_text(audit)
original = (B / 'CliffordContraction.lean').read_text()
old = 'K R = algebraMap ℝ Cl (-scal R)'
assert original.count(old) == 1
(G / 'replay-sources/FalseMainSign.lean').write_text(original.replace(old, 'K R = algebraMap ℝ Cl (scal R)'))
(G / 'replay-sources/FalseSectional.lean').write_text('''import CliffordControls
open GUClifford
example : K sectional = algebraMap ℝ Cl 2 := sectional_K
''')
(G / 'replay-sources/FalseWithoutBianchi.lean').write_text('''import CliffordControls
open GUClifford
example : K fourform = algebraMap ℝ Cl (-scal fourform) := by
  exact actual_clifford_contraction fourform fourform_pair
''')

(G / 'cache').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='independent-', dir=G / 'cache') as work:
    work = Path(work)
    env['LEAN_PATH'] = str(work) + ':' + ':'.join(paths)
    for file in (G / 'replay-sources').glob('*.lean'):
        (work / file.name).write_bytes(file.read_bytes())
    for m in MODULES:
        assert digest(work / (m + '.lean')) == before[m + '.lean']
        run('fresh-' + m, [lean, '--root=' + str(work), '-o', str(work / (m + '.olean')), str(work / (m + '.lean'))], work)
    output = run('all-public-axioms', [lean, str(work / 'Audit.lean')], work)
    axioms = {name: [s.strip() for s in ax.split(',') if s.strip()] for name, ax in
              re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output)}
    axioms.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", output)})
    assert set(axioms) == set(names)
    assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in axioms.values())
    for m in MODULES:
        run('kernel-' + m, [str(Path(lean).with_name('leanchecker')), m, '-v'], work)
    run('independent-client', [lean, '--root=' + str(work), '-o', str(work / 'IndependentClient.olean'), str(work / 'IndependentClient.lean')], work)
    run('kernel-independent-client', [str(Path(lean).with_name('leanchecker')), 'IndependentClient', '-v'], work)
    for name in ['FalseMainSign', 'FalseSectional', 'FalseWithoutBianchi']:
        output = run('negative-' + name, [lean, str(work / (name + '.lean'))], work, succeeds=False)
        assert 'unsolved goals' in output or 'Type mismatch' in output or 'Application type mismatch' in output
        assert 'unknown identifier' not in output.lower() and 'unknown module' not in output.lower()

after = inventory()
assert after == before
(G / 'hashes-after.json').write_text(json.dumps(after, indent=2) + '\n')
result = {'accepted': True, 'frozen_builder_manifest': MANIFEST, 'builder_files_unchanged': 34,
          'fresh_modules': MODULES, 'public_theorems_audited': len(names), 'axioms': axioms,
          'lean': version, 'mathlib_revision': revision, 'steps': steps,
          'scope': 'Fresh target modules, four separate module kernel replays, plus an independent exact-statement and mixed-sign client. Pinned prebuilt Mathlib reused.'}
(G / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'accepted': True, 'public_theorems_audited': len(names), 'builder_files_unchanged': 34}), flush=True)
