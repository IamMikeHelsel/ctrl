#!/usr/bin/env python3
"""Read-only input checks; writes only this E9 packet's INPUTS.json."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'lean-controls').is_dir())
BASE = HERE.parent.parent
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    old = json.loads((HERE.parent / 'weighted-profile-08/INPUTS.json').read_text())['prior_freezes']
    old.append({'manifest': 'research/pods/2026-10-18/method-transfer-01/erdos/weighted-profile-08/artifact-sha256.json',
                'sha256': 'fe60ad304a8e66638b31bce37677ee158c52135b08a4aa128a59c03c58987e26'})
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
             BASE / 'root-review/FINITE-GRAPH-BRIDGE-CARD.txt',
             BASE / 'critic/milestone-11/finite-graph-gate/REPORT.txt',
             BASE / 'critic/milestone-11/finite-graph-gate/manifest.json',
             HERE.parent / 'saving-replay-03/INPUTS.json',
             HERE.parent / 'comparison-02/source-dependencies.json',
             HERE.parent / 'free-slope-05/PROOF.txt',
             ROOT / 'lean-controls/lean-toolchain', ROOT / 'lean-controls/lake-manifest.json']
    files = {str(p.relative_to(ROOT)): sha(p) for p in paths}
    assert sha(paths[4]) == '83df9d90ffc596c3a2092a66dbfb22944d6332fc5e4aab2132eb1b46c4774243'
    accepted = BASE / 'critic/milestone-12/weighted-profile-review/manifest.json'
    assert sha(accepted) == '4bbc1207021b8e5aff4575d78d7d398707772cf77c21786e2b060ff01899eb14'
    files[str(accepted.relative_to(ROOT))] = sha(accepted)
    e8 = HERE.parent / 'weighted-profile-08/WeightedProfiles.lean'
    assert sha(HERE / 'WeightedProfiles.lean') == sha(e8)
    files[str(e8.relative_to(ROOT))] = sha(e8)

    copies = []
    for cp, orig in [('source-inputs/card.txt', paths[2]),
                     ('source-inputs/statement-gate.txt', paths[3]),
                     ('source-inputs/executed-lean-toolchain', paths[8]),
                     ('source-inputs/executed-lake-manifest.json', paths[9])]:
        assert sha(HERE / cp) == sha(orig)
        copies.append({'copy': cp, 'original': str(orig.relative_to(ROOT)),
                       'sha256': sha(HERE / cp), 'byte_identical': True})
    upstream = []
    for name in ['GraphBasics', 'GraphRational', 'ExternalInputs', 'LowDensityGraph', 'WeightedGraph', 'CubicNeighborhood', 'OneStepSaving', 'LowDensityConstruction']:
        p = HERE / f'upstream-original/Erdos128/{name}.lean'
        prior = ROOT / f'research/opportunity-assessment/sources/erdos128/lean/Erdos128/{name}.lean'
        assert sha(p) == sha(prior)
        upstream.append({'module': 'Erdos128.' + name, 'copy': str(p.relative_to(HERE)),
                         'upstream_source': str(prior.relative_to(ROOT)), 'sha256': sha(p),
                         'byte_identical': True, 'executed_in_fresh_closure': name != 'LowDensityConstruction', 'direct_imports': re.findall(r'^import (.+)$', p.read_text(), re.M)})
    for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']:
        p = HERE / 'upstream-original' / name
        prior = ROOT / 'research/opportunity-assessment/sources/erdos128/lean' / name
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
              'upstream_module_patch': None, 'extracted_helper_patch': 'CutHelpers.patch', 'prior_freezes': checks,
              'prior_files_verified': sum(x['files_checked'] for x in checks)}
    (HERE / 'INPUTS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'prior_packets': len(checks), 'prior_files': result['prior_files_verified'],
                      'all_intact': True, 'unchanged_upstream_modules': len(upstream)}, indent=2))
if __name__ == '__main__':
    main()
