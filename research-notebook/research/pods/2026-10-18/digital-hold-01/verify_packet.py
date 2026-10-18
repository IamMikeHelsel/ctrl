#!/usr/bin/env python3
"""Check frozen evidence identity and review bindings; does not rerun Lean."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

REL = Path('research/pods/2026-10-18/digital-hold-01')
PINS = {
    'builder': '79f0478d50e4bbe346f964e3c2b737c2729b8287ff0734d476e9789ce449787c',
    'critic': '9c52bb05810054f73134494d67bf304085ed11b846cab6221c8d06d20db6c479',
    'grader': '97a3bcb6d7731078204cd2173e477fa5eb9646d655f9c8d469d9045c092a0085',
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_files(base, entries):
    for name, entry in entries.items():
        want = entry['sha256'] if isinstance(entry, dict) else entry
        path = base / name
        if not path.is_file() or digest(path) != want:
            raise ValueError(f'Hash mismatch or missing file: {path}')
    return len(entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    pod = args.workspace / REL
    counts = {}
    for role, want in PINS.items():
        manifest = pod / role / 'artifact-sha256.json'
        if digest(manifest) != want:
            raise ValueError(f'Frozen {role} manifest changed')
        counts[role] = check_files(manifest.parent, json.loads(manifest.read_text())['files'])
    counts['builder_inputs'] = check_files(args.workspace, json.loads((pod/'builder/input-sha256.json').read_text()))
    counts['grader_inputs'] = check_files(args.workspace, json.loads((pod/'grader/input-bindings.json').read_text())['sha256'])
    critic = json.loads((pod/'critic/review-results.json').read_text())
    replay = json.loads((pod/'critic/replay-results.json').read_text())
    grade = json.loads((pod/'grader/final-review-results.json').read_text())
    assert critic['verdict'] == grade['independent_critic_verdict']
    assert critic['verdict'].startswith('ACCEPT bounded conditional fresh-start')
    assert not critic['proof_repair_required']
    assert replay['passed'] and replay['fresh_source_unchanged']
    assert all(step['passed'] for step in replay['steps'])
    assert len(replay['steps']) == critic['replay_steps'] == 12
    assert len(replay['axioms']) == critic['theorems_audited'] == 39
    assert all(set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'} for ax in replay['axioms'].values())
    assert all(value.startswith('MET within the declared conditional scope') for value in grade['criteria'].values())
    assert set(grade['criteria']) == {f'A{i}' for i in range(1,7)}
    check_files(pod/'critic', grade['critic_evidence_sha256'])
    for role in ('builder', 'critic'):
        assert grade['binding_checks'][role]['manifest_sha256'] == PINS[role]
    for module, sha in replay['source_sha256'].items():
        assert digest(pod/'builder'/f'{module}.lean') == sha
        assert digest(pod/'critic/fresh'/f'{module}.lean') == sha
    report = {'utc': datetime.now(timezone.utc).isoformat(), 'passed': True,
              'workspace': str(args.workspace.resolve()), 'entries_verified': counts,
              'manifest_sha256': PINS, 'critic_verdict': critic['verdict'],
              'scope': 'Hash and review-binding check. Lean replay is recorded separately in critic/replay-results.json.'}
    data = json.dumps(report, indent=2)+'\n'
    if args.output:
        if args.output.exists():
            raise ValueError('Use a new output path; frozen verification records are not overwritten')
        args.output.write_text(data)
    print(data)


if __name__ == '__main__':
    main()
