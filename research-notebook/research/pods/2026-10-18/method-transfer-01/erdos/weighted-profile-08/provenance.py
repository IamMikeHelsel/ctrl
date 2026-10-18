#!/usr/bin/env python3
"""Read-only input checks; writes only this E8 packet's INPUTS.json."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'lean-controls').is_dir())
BASE = HERE.parent.parent
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    old = json.loads((HERE.parent / 'global-cut-07/INPUTS.json').read_text())['prior_freezes']
    old.append({'manifest': 'research/pods/2026-10-18/method-transfer-01/erdos/global-cut-07/artifact-sha256.json',
                'sha256': 'f01bd98d9def8bf80cd169f94732a1228562dec23ca1e204f6526a82fce9f749'})
    checks = []
    for item in old:
        p = ROOT / item['manifest']
        assert sha(p) == item['sha256'], p
        data = json.loads(p.read_text())
        for rel, h in data['files'].items():
            assert sha(p.parent / rel) == h, (p, rel)
        checks.append({'manifest': item['manifest'], 'sha256': sha(p),
                       'files_checked': len(data['files']), 'all_match': True})
    paths = [ROOT / 'AGENTS.md', BASE / 'CHARTER.txt',
             BASE / 'root-review/WEIGHTED-PROFILE-BRIDGE-CARD.txt',
             BASE / 'critic/milestone-08/weighted-profile-gate/REPORT.txt',
             BASE / 'critic/milestone-08/weighted-profile-gate/manifest.json',
             HERE.parent / 'saving-replay-03/INPUTS.json',
             HERE.parent / 'comparison-02/source-dependencies.json',
             HERE.parent / 'free-slope-05/PROOF.txt',
             ROOT / 'lean-controls/lean-toolchain', ROOT / 'lean-controls/lake-manifest.json']
    files = {str(p.relative_to(ROOT)): sha(p) for p in paths}
    copies = []
    for cp, orig in [('source-inputs/root-card.txt', paths[2]),
                     ('source-inputs/accepted-statement-preflight.txt', paths[3]),
                     ('source-inputs/executed-lean-toolchain', paths[8]),
                     ('source-inputs/executed-lake-manifest.json', paths[9])]:
        assert sha(HERE / cp) == sha(orig)
        copies.append({'copy': cp, 'original': str(orig.relative_to(ROOT)),
                       'sha256': sha(HERE / cp), 'byte_identical': True})
    upstream = []
    for name in ['WeightedGraph', 'CubicNeighborhood', 'OneStepSaving']:
        p = HERE / f'upstream-source/Erdos128/{name}.lean'
        prior = HERE.parent / f'saving-replay-03/original/Erdos128/{name}.lean'
        assert sha(p) == sha(prior)
        upstream.append({'module': 'Erdos128.' + name, 'copy': str(p.relative_to(HERE)),
                         'e3_source': str(prior.relative_to(ROOT)), 'sha256': sha(p),
                         'byte_identical': True, 'direct_imports': re.findall(r'^import (.+)$', p.read_text(), re.M)})
    for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']:
        p = HERE / 'upstream-source' / name
        prior = HERE.parent / 'saving-replay-03/original' / name
        assert sha(p) == sha(prior)
        copies.append({'copy': str(p.relative_to(HERE)), 'original': str(prior.relative_to(ROOT)),
                       'sha256': sha(p), 'byte_identical': True})
    result = {'recorded_utc': datetime.now(timezone.utc).isoformat(), 'files': files, 'copies': copies,
              'upstream_repository': 'https://github.com/aimir/erdos-128-sparse-halves',
              'upstream_revision': 'ba85f319ebb33ec2194ef4c2929a12916329e1e7',
              'upstream_modules': upstream, 'declared_toolchain': 'leanprover/lean4:v4.30.0',
              'declared_mathlib': 'c5ea00351c28e24afc9f0f84379aa41082b1188f',
              'executed_toolchain': 'leanprover/lean4:v4.35.0',
              'executed_mathlib': '56a005855ea17e0b0958f73ec801ae140b0a1679',
              'upstream_patch': None, 'prior_freezes': checks,
              'prior_files_verified': sum(x['files_checked'] for x in checks)}
    (HERE / 'INPUTS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'prior_packets': len(checks), 'prior_files': result['prior_files_verified'],
                      'all_intact': True, 'unchanged_upstream_modules': len(upstream)}, indent=2))
if __name__ == '__main__':
    main()
