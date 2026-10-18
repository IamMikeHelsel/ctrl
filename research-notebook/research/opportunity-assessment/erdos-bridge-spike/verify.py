#!/usr/bin/env python3
"""Rebuild only this graph bridge against existing pinned mathlib dependencies."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
parser = argparse.ArgumentParser()
parser.add_argument('--toolchain-bin', type=Path, default=Path.home() /
                    '.elan/toolchains/leanprover--lean4---v4.35.0/bin')
args = parser.parse_args()
cache = WORKSPACE / 'lean-controls/.lake/packages'
dependency_paths = sorted(p / '.lake/build/lib/lean' for p in cache.iterdir()
                          if (p / '.lake/build/lib/lean').is_dir())
if not (cache / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file():
    raise SystemExit('Pinned cached mathlib is unavailable; no installation attempted.')
env = os.environ.copy()
env['PATH'] = str(args.toolchain_bin) + os.pathsep + env.get('PATH', '')
env['LEAN_PATH'] = os.pathsep.join(map(str, [HERE, *dependency_paths]))
sources = [HERE / 'Erdos128/GraphBasics.lean', HERE / 'DeletionBridge.lean']
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
before = {str(p.relative_to(HERE)): digest(p) for p in sources}
result = {'date': '2026-10-17', 'sources_before': before,
          'scope': 'graph deletion/restoration glue; completion existence is an explicit premise',
          'dependency_policy': 'existing pinned mathlib/package artifacts; no original controls oleans',
          'lean_path': env['LEAN_PATH'], 'runs': []}
result['lean'] = subprocess.check_output([str(args.toolchain_bin / 'lean'), '--version'],
                                       cwd=HERE, env=env, text=True).strip()
result['mathlib_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                            cwd=cache / 'mathlib', text=True).strip()
modules = ['Erdos128.GraphBasics', 'DeletionBridge']
for module, source in zip(modules, sources):
    command = [str(args.toolchain_bin / 'lean'), '-o',
               str(source.relative_to(HERE).with_suffix('.olean')), str(source.relative_to(HERE))]
    start = time.monotonic()
    run = subprocess.run(command, cwd=HERE, env=env, text=True, capture_output=True)
    log = 'verified-' + module.replace('.', '-') + '.log'
    (HERE / log).write_text(run.stdout + run.stderr)
    result['runs'].append({'command': command, 'exit': run.returncode,
                           'seconds': time.monotonic() - start, 'log': log})
    if run.returncode:
        (HERE / 'verification.json').write_text(json.dumps(result, indent=2))
        raise SystemExit(run.returncode)
    if module == 'DeletionBridge':
        matches = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", run.stdout)
        result['axioms'] = {name: [a.strip() for a in axioms.split(',')]
                            for name, axioms in matches}
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        if len(matches) != 7 or any(set(a) - allowed for a in result['axioms'].values()):
            raise SystemExit('Unexpected axiom audit or missing theorem audit.')
start = time.monotonic()
command = [str(args.toolchain_bin / 'leanchecker'), *modules, '-v']
run = subprocess.run(command, cwd=HERE, env=env, text=True, capture_output=True)
(HERE / 'verified-kernel-replay.log').write_text(run.stdout + run.stderr)
result['runs'].append({'command': command, 'exit': run.returncode,
                       'seconds': time.monotonic() - start, 'log': 'verified-kernel-replay.log'})
result['kernel_replay_scope'] = 'replay both local modules into their import environments; cached mathlib trusted'
result['sources_after'] = {str(p.relative_to(HERE)): digest(p) for p in sources}
result['source_stable'] = result['sources_after'] == before
result['passed'] = run.returncode == 0 and result['source_stable']
(HERE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'passed': result['passed'], 'new_theorems': len(result['axioms']),
                  'seconds': sum(r['seconds'] for r in result['runs'])}))
raise SystemExit(0 if result['passed'] else 1)
