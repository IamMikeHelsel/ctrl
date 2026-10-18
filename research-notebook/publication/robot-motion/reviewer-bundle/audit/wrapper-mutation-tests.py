#!/usr/bin/env python3
"""Four packaging checks. These are not new Lean proof negative controls."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, tempfile

HERE = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--dependency-project', required=True, type=Path)
parser.add_argument('--lake', required=True, type=Path)
parser.add_argument('--elan-home', type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=False)
manifest = json.loads((HERE / 'input-manifest.json').read_text())
results = []
cases = [
    ('source-changed', 'src/Kernel.lean', False, 'Changed input: src/Kernel.lean'),
    ('source-hash-refreshed', 'src/LeanControls/Discrete.lean', True, 'Original source hash: LeanControls.Discrete'),
    ('fixture-hash-refreshed', 'inputs/reference-checks.json', True, 'Fixture input binding: inputs/reference-checks.json'),
    ('dependency-pin-changed', None, False, 'Dependency project pin mismatch: lean-toolchain'),
]
for label, filename, refresh, expected in cases:
    with tempfile.TemporaryDirectory(prefix='wrapper-copy-', dir=out) as tmp:
        root = Path(tmp)
        for name in list(manifest['files']) + ['input-manifest.json']:
            dst = root / name
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(HERE / name, dst)
        dependency = args.dependency_project.resolve()
        if filename:
            p = root / filename
            p.write_bytes(p.read_bytes() + b'\n')
            if refresh:
                m = json.loads((root / 'input-manifest.json').read_text())
                m['files'][filename] = hashlib.sha256(p.read_bytes()).hexdigest()
                (root / 'input-manifest.json').write_text(json.dumps(m))
        else:
            dependency = root / 'changed-dependency-project'
            shutil.copytree(HERE / 'dependency-project', dependency)
            (dependency / 'lean-toolchain').write_text('leanprover/lean4:v4.35.1\n')
        command = ['python3', str(root / 'replay.py'), '--dependency-project', str(dependency),
                   '--lake', str(args.lake.absolute()), '--output', str(root / 'must-not-build')]
        if args.elan_home:
            command += ['--elan-home', str(args.elan_home.resolve())]
        r = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=30)
        log = out / (label + '.log')
        log.write_text(r.stdout)
        passed = r.returncode != 0 and expected in r.stdout and not (root / 'must-not-build').exists()
        results.append({'case': label, 'passed': passed, 'exit_code': r.returncode,
                        'expected_rejection': expected,
                        'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()})
        if not passed:
            raise RuntimeError('Mutation test did not fail as expected: ' + label)
(out / 'results.json').write_text(json.dumps({'passed': True, 'kind': 'wrapper mutation controls, not Lean theorems',
                                           'cases': results}, indent=2) + '\n')
print('PASS: four wrapper mutations rejected before build')
