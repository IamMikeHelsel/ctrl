#!/usr/bin/env python3
"""Recheck the fixed shared-witness source; does not perform SOS discovery.
Run from any directory. Requires the pinned SOS checkout and cached dependencies.
"""
from pathlib import Path
import hashlib
import json
import os
import statistics
import subprocess
import sys
import time

out = Path(__file__).resolve().parent
workspace = out.parent.parent
root = workspace / 'research/sos-comparison'
sys.path.insert(0, str(workspace / 'lean-controls/scripts'))
from lean_runtime import runtime
lake, env = runtime(workspace / 'lean-controls')
module = 'SOSTest.SOSSharedWitnessReplay'
source = root / 'SOSTest/SOSSharedWitnessReplay.lean'
if not source.exists():
    raise RuntimeError('Prepare the pinned SOS checkout and copy VerifiedSOSReplay.lean '
                       'to SOSTest/SOSSharedWitnessReplay.lean; see REPRODUCE.txt.')
assert source.read_bytes() == (out / 'SOSSharedWitnessReplay.lean').read_bytes()

def run(stage, args):
    started = time.perf_counter()
    process = subprocess.run([str(lake), *args], cwd=root, env=env,
                             text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=120)
    elapsed = time.perf_counter() - started
    (out / f'{stage}.log').write_text(process.stdout)
    result = {'stage': stage, 'elapsed_seconds': elapsed,
              'exit_code': process.returncode, 'command': [str(lake), *args]}
    if process.returncode != 0 or 'sorryAx' in process.stdout:
        raise RuntimeError(f'{stage} failed; inspect log')
    if "depends on axioms: [propext, Classical.choice, Quot.sound]" not in process.stdout:
        raise RuntimeError(f'{stage}: expected axiom report was absent')
    return result

build = run('SOSSharedWitnessBuild', ['build', module])
setup = '.lake/build/ir/SOSTest/SOSSharedWitnessReplay.setup.json'
runs = [run(f'SOSReplay{i}', ['env', 'lean', str(source), f'--setup={setup}'])
        for i in range(1, 4)]
times = [r['elapsed_seconds'] for r in runs]
results = {'status': 'checked', 'witness_origin': 'translated existing Bernstein witness; no independent solver discovery',
           'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'source_bytes_utf8': len(source.read_bytes()),
           'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
           'initial_build': build, 'fresh_process_replays': runs,
           'replay_median_seconds': statistics.median(times),
           'replay_min_seconds': min(times), 'replay_max_seconds': max(times),
           'timing_boundary': 'wall clock from launching lake through Lean exit, includes imports and axiom query; dependencies prebuilt; fresh Lean process per replay; OS caches warm'}
(out / 'SOSReplayResults.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
