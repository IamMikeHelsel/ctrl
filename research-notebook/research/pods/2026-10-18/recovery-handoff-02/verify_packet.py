#!/usr/bin/env python3
"""Verify frozen identities and independent review bindings. Does not run Lean."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

REL = Path('research/pods/2026-10-18/recovery-handoff-02')
PINS = {
    'handoff-builder/artifact-sha256.json': '0ca3f54c0d77ff244866bb5a861c6d701749594d6d155c87ba9ab7338e23276e',
    'critic/handoff/artifact-sha256.json': 'ec92eed5516d41a82a1a52c2977a773783513f700d8034c9eb03cd7e4409d2b9',
    'grip-builder/frozen-manifest.json': 'c51f6effdb28ed5dcd31b0dd9079e9258f48d697ae4c59643f7ffa67060f7a90',
    'grip-builder/preflight-manifest.json': 'e7cd5e352f6d96603ffe159c5e20a43db7c1d267adfc60fac8147dfaffc09ec3',
    'critic/grip/artifact-sha256.json': '24771f80d1bec51fc6438e1e82373facc99729595e46b69adc9e309c5b7d2e50',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def files(base, entries):
    for name, entry in entries.items():
        expected = entry['sha256'] if isinstance(entry, dict) else entry
        require(digest(base / name) == expected, f'Changed file: {base / name}')
    return len(entries)


def replay_checks(folder, result):
    require(result['passed'] and result['source_unchanged'], 'Replay did not pass unchanged')
    require(all(step['passed'] for step in result['steps']), 'A replay step failed')
    require(all(set(a) <= ALLOWED for a in result['axioms'].values()), 'Unexpected axiom')
    for step in result['steps']:
        require(digest(folder / 'logs' / (step['label'] + '.log')) == step['log_sha256'],
                'Replay log does not match result')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    pod = args.workspace / REL
    counts = {}
    for name, expected in PINS.items():
        manifest = pod / name
        require(digest(manifest) == expected, f'Manifest changed: {name}')
        counts[name] = files(manifest.parent, read(manifest)['files'])

    counts['handoff inputs'] = files(args.workspace, read(pod / 'handoff-builder/input-provenance.json')['inputs'])
    prov = read(pod / 'grip-builder/SOURCE-PROVENANCE.json')
    for item in prov['local_predecessors'].values():
        require(digest(args.workspace / item['source']) == item['sha256'], 'Predecessor changed')
        require(digest(pod / 'grip-builder' / item['copy']) == item['sha256'], 'Copied predecessor changed')
    counts['recovery predecessors'] = len(prov['local_predecessors'])

    handoff = read(pod / 'critic/handoff/review-results.json')
    replay = read(pod / 'critic/handoff/replay-results.json')
    require(handoff['verdict'] == 'ACCEPT two fixed-case conditional delayed digital holding results',
            'Handoff independent acceptance is missing')
    require(not handoff['proof_repair_required'], 'Unintegrated handoff repair')
    require(handoff['frozen_builder_manifest_sha256'] == PINS['handoff-builder/artifact-sha256.json'],
            'Handoff acceptance binds a different builder')
    require(len(replay['steps']) == handoff['replay_steps'] == 20, 'Handoff replay count differs')
    require(len(replay['axioms']) == handoff['theorems_audited'] == 100, 'Handoff audit differs')
    require(replay['toolchain_pins_match_builder'], 'Handoff pin mismatch')
    replay_checks(pod / 'critic/handoff', replay)
    files(pod, handoff['ancillary_outputs_inspected_sha256'])
    require(digest(pod / 'critic/replay_handoff.py') == handoff['replay_script_sha256'], 'Handoff replay script changed')
    for module, sha in replay['source_sha256'].items():
        source = pod / 'handoff-builder' / ('inputs' if module == 'DigitalHold' else '') / (module + '.lean')
        require(digest(source) == digest(pod / 'critic/handoff/fresh' / (module + '.lean')) == sha,
                'Handoff source/copy mismatch')
    for key, path in [('lean_toolchain_sha256', 'lean-controls/lean-toolchain'),
                      ('lake_manifest_sha256', 'lean-controls/lake-manifest.json')]:
        require(digest(args.workspace / path) == replay[key], 'Retained project pin changed')

    folder = pod / 'critic/grip'
    grip = read(folder / 'review-results.json')
    recovery = read(folder / 'replay-results.json')
    extra = read(folder / 'extra-checks.json')
    builder = read(pod / 'grip-builder/verification.json')
    require(grip['verdict'] == 'ACCEPT conditional model theorem; no builder repair',
            'Recovery independent acceptance is missing')
    require(grip['builder_manifest_sha256'] == PINS['grip-builder/frozen-manifest.json'],
            'Recovery acceptance binds a different builder')
    require(digest(pod / 'grip-builder/verification.json') == grip['builder_verification_sha256'],
            'Builder verification differs')
    for field, name in [('report_sha256', 'REPORT.txt'), ('replay_results_sha256', 'replay-results.json'),
                        ('extra_checks_sha256', 'extra-checks.json')]:
        require(digest(folder / name) == grip[field], 'Recovery acceptance evidence differs')
    replay_checks(folder, recovery)
    require(extra['passed'] and all(s['passed'] for s in extra['steps']), 'Extra recovery check failed')
    for step in extra['steps']:
        require(digest(folder / 'logs' / (step['label'] + '.log')) == step['log_sha256'],
                'Extra replay log differs')
    require(len(recovery['steps']) == grip['accepted_main_steps'] == 84, 'Main recovery count differs')
    require(len(extra['steps']) == grip['accepted_extra_steps'] == 3, 'Extra recovery count differs')
    require(len(recovery['axioms']) == grip['theorem_axiom_closures'] == 27, 'Recovery audit differs')
    require(recovery['core_source_unchanged'] and recovery['toolchain_pins_match_builder'],
            'Recovery dependency or pin mismatch')
    require(len(recovery['core_source_sha256']) == grip['local_dependency_count'] == 31,
            'Local dependency closure differs')
    require(len(recovery['source_sha256']) == grip['research_module_count'] == 6,
            'Research module count differs')
    steps = recovery['steps'] + extra['steps']
    require(sum(s['label'].startswith('kernel-') for s in steps) == grip['separate_kernel_checks'] == 39,
            'Recovery kernel coverage differs')
    require(sum(s['expected'] == 'mathematical rejection' for s in steps) == grip['expected_rejections'] == 7,
            'Recovery negative-control coverage differs')
    for module, sha in recovery['source_sha256'].items():
        source = pod / 'grip-builder' / ('' if module.startswith('Recovery') else 'inputs') / (module + '.lean')
        require(digest(source) == digest(folder / 'fresh' / (module + '.lean')) == sha,
                'Recovery source/copy mismatch')
    for module, sha in recovery['core_source_sha256'].items():
        name = module.replace('.', '/') + '.lean'
        require(digest(args.workspace / 'lean-controls' / name) == digest(folder / 'fresh' / name) == sha,
                'Recovery dependency source/copy mismatch')
        require(builder['cached_core_source_sha256']['lean-controls/' + name] == sha,
                'Recovery dependency differs from builder inventory')
    for name, sha in grip['replay_scripts'].items():
        require(digest(pod / 'critic' / name) == sha, 'Recovery replay script changed')
    files(folder / 'fresh', extra['source_sha256'])
    for key in ('lean_toolchain_sha256', 'lake_manifest_sha256', 'lean_sha256', 'leanchecker_sha256'):
        require(recovery[key] == builder[key] == replay[key], 'Replay tool identity differs')

    # Keep the failed critic attempt separate from the accepted replacement.
    require(len(recovery['harness_attempts']) == grip['historical_failed_critic_attempts'] == 1,
            'Critic failure history differs')
    repair = read(folder / 'critic-test-repair.json')
    attempt = folder / repair['preserved_directory']
    counts['preserved critic attempt'] = files(attempt, repair['preserved_files'])
    prior = read(attempt / 'replay-results.json')
    require(not prior['passed'] and any(not s['passed'] for s in prior['steps']),
            'Historical critic failure is missing')
    accepted_by_label = {s['label']: s for s in recovery['steps']}
    for step in prior['steps']:
        if step['passed']:
            require(accepted_by_label[step['label']] == step, 'Unchanged successful step was rewritten')
    require(repair['after_script_sha256'] == grip['replay_scripts']['replay_grip.py'],
            'Critic repair is not bound to final script')

    counts['root integration'] = files(pod, read(pod / 'root-artifact-sha256.json')['files'])
    report = {'utc': datetime.now(timezone.utc).isoformat(), 'passed': True,
              'workspace': str(args.workspace.resolve()), 'entries_verified': counts,
              'manifest_sha256': PINS, 'handoff_verdict': handoff['verdict'],
              'recovery_verdict': grip['verdict'],
              'scope': 'Frozen identity and independent acceptance binding. Does not rerun Lean.'}
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        require(not args.output.exists(), 'Use a new output path; recorded checks are not overwritten')
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
