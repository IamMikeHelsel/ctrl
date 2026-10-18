#!/usr/bin/env python3
"""Workspace-side assembly. Copy frozen sources; never repair a proof here."""
from pathlib import Path
import hashlib, json, shutil

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[2]
OLD = HERE.parent / 'overnight-reviewer-bundle'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def digest(v): return v['sha256'] if isinstance(v, dict) else v
def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        assert src.read_bytes() == dst.read_bytes(), 'Existing file differs: ' + str(dst)
    else: shutil.copyfile(src, dst)
def write(name, obj):
    p = HERE / name
    text = json.dumps(obj, indent=2) + '\n'
    if p.exists(): assert p.read_text() == text, 'Existing metadata differs: ' + name
    else: p.write_text(text)

def main():
    config = load(HERE / 'assembly-config.json')
    sources, gates, negatives, reviews = {}, {}, {}, {}
    for key, g in config['gates'].items():
        base = WORK / g['folder']
        manifest = base / g['manifest']
        assert sha(manifest) == g['manifest_sha256'], key
        files = load(manifest)['files']
        closure = base / g['closure']
        assert sha(closure) == digest(files[g['closure']]), key
        copy(manifest, HERE / 'provenance' / key / 'manifest.json')
        copy(closure, HERE / 'provenance' / key / 'closure.json')
        gates[key] = {'manifest_sha256': g['manifest_sha256'], 'original_closure_name': g['closure']}
        for module, item in load(closure).items():
            src = WORK / item['path']
            assert sha(src) == item['sha256'], module
            if module in sources: assert sources[module]['sha256'] == item['sha256'], module
            info = {'path': 'src/' + module.replace('.', '/') + '.lean', 'sha256': item['sha256'],
                    'original_path': item['path'], 'gate': key}
            copy(src, HERE / info['path'])
            sources[module] = info
        for original in g['negatives']:
            src = base / original
            assert sha(src) == digest(files[original]), original
            dest = 'negative-controls/' + key + '/' + src.name
            assert dest not in negatives, dest
            copy(src, HERE / dest)
            negatives[dest] = {'gate': key, 'original_path': original, 'sha256': sha(src)}
        review = g['review']; rbase = WORK / review['folder']
        rm = rbase / review['manifest']
        assert sha(rm) == review['manifest_sha256'], key
        rfiles = load(rm)['files']
        copy(rm, HERE / 'provenance' / key / 'review' / 'manifest.json')
        for name in review['reports']:
            assert sha(rbase / name) == digest(rfiles[name]), name
            copy(rbase / name, HERE / 'provenance' / key / 'review' / name)
        reviews[key] = {'manifest_sha256': review['manifest_sha256'], 'reports': review['reports']}
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        copy(WORK / 'lean-controls' / name, HERE / 'dependency-project' / name)
    binding = {'gates': gates, 'modules': sources, 'negative_controls': negatives,
               'roots': config['roots'], 'kernel_targets': config['kernel_targets']}
    write('source-bindings.json', binding); write('review-bindings.json', reviews)
    old = (OLD / 'replay.py').read_text()
    start = old.index('GATE_HASHES = '); end = old.index('def require(', start)
    fixed = 'GATE_HASHES = ' + repr({k:v['manifest_sha256'] for k,v in gates.items()}) + '\n'
    fixed += "PIN = '56a005855ea17e0b0958f73ec801ae140b0a1679'\n"
    fixed += 'REVIEW_HASHES = ' + repr({k:v['manifest_sha256'] for k,v in reviews.items()}) + '\n'
    fixed += 'EXPECTED_ROOTS = ' + repr(config['roots']) + '\n'
    fixed += 'EXPECTED_KERNEL_TARGETS = ' + repr(config['kernel_targets']) + '\n'
    fixed += 'EXPECTED_NEGATIVE_CONTROLS = ' + repr(negatives) + '\n'
    fixed += 'EXPECTED_BINDINGS_SHA256 = ' + repr(sha(HERE / 'source-bindings.json')) + '\n'
    fixed += 'EXPECTED_REVIEW_BINDINGS_SHA256 = ' + repr(sha(HERE / 'review-bindings.json')) + '\n'
    old = old[:start] + fixed + old[end:]
    old = old.replace('frozen 50-module proof closure', f'frozen {len(sources)}-module proof closure')
    old = old.replace("'lean_sha256': sha(lean),", "'lean_executable': str(lean), 'checker_executable': str(checker), 'lean_sha256': sha(lean),")
    old = old.replace('and len(union) == 50', f'and len(union) == {len(sources)}')
    old = old.replace("require(out != HERE and not any(out == p or out in p.parents for p in sources.values()), 'Output overlaps inputs')", "require(out != HERE and HERE not in out.parents and not any(out == p or out in p.parents for p in sources.values()), 'Output overlaps inputs')")
    old = old.replace("require(len(binding['negative_controls']) == 12, 'Negative control coverage')",
        "require(binding['negative_controls'] == EXPECTED_NEGATIVE_CONTROLS, 'Negative control plan')")
    marker = "    binding = load(HERE / 'source-bindings.json')\n"
    assert old.count(marker) == 1
    old = old.replace(marker, marker + "    require(sha(HERE / 'source-bindings.json') == EXPECTED_BINDINGS_SHA256, 'Source binding plan')\n"
        "    require(sha(HERE / 'review-bindings.json') == EXPECTED_REVIEW_BINDINGS_SHA256, 'Review binding plan')\n"
        "    require(binding['roots'] == EXPECTED_ROOTS, 'Root plan')\n"
        "    require(binding['kernel_targets'] == EXPECTED_KERNEL_TARGETS, 'Kernel replay plan')\n")
    marker = "        report.update(passed=True, local_modules=len(sources), kernel_replays=len(binding['kernel_targets']),\n"
    assert old.count(marker) == 1
    old = old.replace(marker, "        report['compiled_objects'] = {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob('*')) if p.is_file() and '.olean' in p.name}\n"
        "        report['compiled_module_names'] = list(sources)\n" + marker)
    target = HERE / 'replay.py'
    if target.exists(): assert target.read_text() == old
    else: target.write_text(old)
    print(json.dumps({'modules': len(sources), 'gates': len(gates), 'negative_controls': len(negatives),
                      'kernel_targets': len(config['kernel_targets'])}))

if __name__ == '__main__': main()
