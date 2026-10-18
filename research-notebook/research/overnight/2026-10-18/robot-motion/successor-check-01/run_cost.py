"""Local exploratory timings. Never writes in the frozen proof folder."""
from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import os
import platform
import subprocess
import time

HERE = Path(__file__).resolve().parent
BUILDER = HERE


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if (HERE / 'results.json').exists():
        raise RuntimeError('Preserve the original run; use a new sibling copy.')
    spec = importlib.util.spec_from_file_location('proof_env', BUILDER / 'dev.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    env, lean, deps = helper.environment()
    deps = os.pathsep.join(x for x in deps.split(os.pathsep) if Path(x).resolve() != (helper.BASE/'.lake/build/lib/lean').resolve())
    env['LEAN_PATH'] = str(BUILDER / '.cache/fresh') + os.pathsep + deps
    bound = {
        str(p.relative_to(HERE.parent)): sha(p)
        for p in [HERE / 'Benchmark.lean', HERE / 'protocol.txt', HERE / 'run_cost.py',
                  BUILDER / 'SuccessorGuard.lean', BUILDER / 'source-freeze.json']
    }
    (HERE / 'pre-run-freeze.json').write_text(json.dumps(bound, indent=2) + '\n')
    data = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'platform': platform.platform(), 'machine': platform.machine(),
            'execution': 'Lean --run; shared active host; internal result print included',
            'lean': lean, 'lean_sha256': sha(Path(lean)), 'binding': bound, 'rows': []}
    for n in [1, 2, 4, 8, 16, 32]:
        for repetition in range(1, 4):
            started = time.monotonic()
            row = {'events': n, 'repetition': repetition}
            try:
                result = subprocess.run(
                    [lean, '--run', str(HERE / 'Benchmark.lean'), str(n)],
                    cwd=HERE, env=env, text=True, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, timeout=30,
                )
                row.update({'status': 'completed' if result.returncode == 0 else 'error',
                            'exit_code': result.returncode, 'output': result.stdout})
                for line in result.stdout.splitlines():
                    if line.startswith('accepted='):
                        row['accepted'] = line.split('=', 1)[1] == 'true'
                    if line.startswith('nanoseconds='):
                        row['checker_nanoseconds_including_print'] = int(line.split('=', 1)[1])
            except subprocess.TimeoutExpired:
                row['status'] = 'timeout'
            row['process_seconds'] = time.monotonic() - started
            data['rows'].append(row)
            (HERE / 'results.json').write_text(json.dumps(data, indent=2) + '\n')
            print(json.dumps(row), flush=True)
            if row['status'] == 'error':
                raise RuntimeError('Implementation error; preserve failed attempt.')
    assert all(sha(HERE.parent / p) == value for p, value in bound.items())
    data['inputs_unchanged'] = True
    data['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (HERE / 'results.json').write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
