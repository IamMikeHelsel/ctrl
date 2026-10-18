#!/usr/bin/env python3
"""Copy exact frozen proof inputs. Workspace-side assembly, not the replay tool."""
from pathlib import Path
import hashlib, json, shutil

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[2]
POD = WORK / 'research/overnight/2026-10-18/robot-motion'
GATES = {
    'physical-arrival': ('builder-02', '3abb293d650c12e90e1f36dc6296b0b81a2dbbe570692ed4ffdaaaa9f0dacf20', 'source-closure-02.json'),
    'history-pruning': ('history-pruning-01', '854f736b05dd0a90608b75a6b89dc0230aaa7fa064f1461b62563808b8a5d288', 'source-closure.json'),
    'successor-check': ('successor-check-01', '006e5fee639c1eff6ce90d5e49945f2003ac47dc5155b7af8f4f265526ab856d', 'source-closure.json'),
}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def stored_hash(v): return v['sha256'] if isinstance(v, dict) else v
def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        assert src.read_bytes() == dst.read_bytes(), f'Existing file differs: {dst}'
    else:
        shutil.copyfile(src, dst)

def main():
    sources, gates, controls = {}, {}, {}
    for key, (folder, digest, closure_name) in GATES.items():
        src = POD / folder
        manifest = src / 'artifact-sha256.json'
        assert sha(manifest) == digest
        files = json.loads(manifest.read_text())['files']
        closure = src / closure_name
        assert sha(closure) == stored_hash(files[closure_name])
        copy(manifest, HERE / 'provenance' / key / 'manifest.json')
        copy(closure, HERE / 'provenance' / key / 'closure.json')
        gates[key] = {'manifest_sha256': digest, 'original_closure_name': closure_name}
        for module, info in json.loads(closure.read_text()).items():
            path = WORK / info['path']
            assert sha(path) == info['sha256']
            if module in sources:
                assert sources[module]['sha256'] == info['sha256'], module
            else:
                sources[module] = {'path': 'src/' + module.replace('.', '/') + '.lean',
                                   'sha256': info['sha256'], 'original_path': info['path'], 'gate': key}
            copy(path, HERE / sources[module]['path'])
        nd = src / ('negative-controls-02' if key == 'physical-arrival' else 'negative-controls')
        for p in sorted(nd.glob('*.lean')):
            original = str(p.relative_to(src))
            assert sha(p) == stored_hash(files[original])
            dest = 'negative-controls/' + key + '/' + p.name
            copy(p, HERE / dest)
            controls[dest] = {'gate': key, 'original_path': original, 'sha256': sha(p)}
    assert len(sources) == 50
    assert len(controls) >= 8
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        copy(WORK / 'lean-controls' / name, HERE / 'dependency-project' / name)
    data = {'gates': gates, 'modules': sources, 'negative_controls': controls,
            'roots': ['PhysicalArrival', 'HistoryPruning', 'SuccessorGuard'],
            'kernel_targets': ['Composition', 'ScaledTracking', 'AccelerationGuard',
                               'AccelerationFixtures', 'ReversalProposal', 'TimedAdmission',
                               'PhysicalArrival', 'HistoryPruning', 'SuccessorGuard']}
    p = HERE / 'source-bindings.json'
    text = json.dumps(data, indent=2) + '\n'
    if p.exists(): assert p.read_text() == text
    else: p.write_text(text)
    print(json.dumps({'modules': len(sources), 'negative_controls': len(controls)}))

if __name__ == '__main__': main()
