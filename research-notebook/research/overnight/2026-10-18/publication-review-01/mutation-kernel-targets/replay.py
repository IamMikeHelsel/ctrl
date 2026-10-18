#!/usr/bin/env python3
"""Replay the frozen 50-module proof closure. Requires Python 3.9+ and pinned Lean caches."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
GATE_HASHES = {
    'physical-arrival': '3abb293d650c12e90e1f36dc6296b0b81a2dbbe570692ed4ffdaaaa9f0dacf20',
    'history-pruning': '854f736b05dd0a90608b75a6b89dc0230aaa7fa064f1461b62563808b8a5d288',
    'successor-check': '006e5fee639c1eff6ce90d5e49945f2003ac47dc5155b7af8f4f265526ab856d',
}
PIN = '56a005855ea17e0b0958f73ec801ae140b0a1679'
REVIEW_HASHES = {
    'physical-arrival': 'fbc7ba5ddeb97c92b788f670fa8c483708366c0c2bfdb7da246128d064df9470',
    'history-pruning': '0fa33fc13c9593ff7cbee6bc3a25c4dd878508558b1d647c5bf9fdfecdd284b0',
    'successor-check': '3620c6af12b074de71d19232ab07db61af2d4f4c191429bae000b23c45f92753',
}
def require(ok, message):
    if not ok: raise RuntimeError(message)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def stored_hash(v): return v['sha256'] if isinstance(v, dict) else v
def now(): return datetime.now(timezone.utc).isoformat()
def local(name):
    p = (HERE / name).resolve()
    require(HERE in p.parents, 'Invalid package path: ' + name)
    return p

def verify_inputs():
    frozen = load(HERE / 'input-manifest.json')
    for name, digest in frozen['files'].items():
        require(sha(local(name)) == digest, 'Changed package input: ' + name)
    binding = load(HERE / 'source-bindings.json')
    require(set(binding['gates']) == set(GATE_HASHES), 'Gate coverage')
    union, manifests = {}, {}
    for key, digest in GATE_HASHES.items():
        manifest = local('provenance/' + key + '/manifest.json')
        require(sha(manifest) == digest == binding['gates'][key]['manifest_sha256'], 'Gate identity: ' + key)
        files = load(manifest)['files']; manifests[key] = files
        closure = local('provenance/' + key + '/closure.json')
        require(sha(closure) == stored_hash(files[binding['gates'][key]['original_closure_name']]), 'Closure binding: ' + key)
        for module, original in load(closure).items():
            if module in union:
                require(union[module]['sha256'] == original['sha256'], 'Conflicting original sources: ' + module)
            union[module] = original
    require(set(union) == set(binding['modules']) and len(union) == 50, 'Module coverage')
    for module, info in binding['modules'].items():
        require(info['path'] == 'src/' + module.replace('.', '/') + '.lean', 'Module path: ' + module)
        require(info['original_path'] == union[module]['path'], 'Original source path: ' + module)
        require(sha(local(info['path'])) == info['sha256'] == union[module]['sha256'], 'Original source hash: ' + module)
    require(len(binding['negative_controls']) == 12, 'Negative control coverage')
    for path, info in binding['negative_controls'].items():
        require(sha(local(path)) == info['sha256'] == stored_hash(manifests[info['gate']][info['original_path']]), 'Negative control binding: ' + path)
    reviews = load(HERE / 'review-bindings.json')
    require(set(reviews) == set(REVIEW_HASHES), 'Review coverage')
    for key, digest in REVIEW_HASHES.items():
        base = HERE / 'provenance' / key / 'review'
        require(sha(base / 'manifest.json') == digest == reviews[key]['manifest_sha256'], 'Review identity: ' + key)
        review_files = load(base / 'manifest.json')['files']
        for name in reviews[key]['reports']:
            require(sha(base / name) == stored_hash(review_files[name]), 'Review report binding: ' + key)
    return frozen, binding

def ordered_sources(binding):
    ordered, visiting = {}, set()
    def visit(module):
        if module in ordered: return
        require(module not in visiting, 'Import cycle: ' + module)
        visiting.add(module)
        path = local(binding['modules'][module]['path'])
        for line in path.read_text().splitlines():
            line = line.removeprefix('public ')
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep in binding['modules']: visit(dep)
                    else: require(dep.split('.')[0] in {'Mathlib','Lean','Init','Std','Batteries','Qq','Aesop'}, 'Unknown external import: ' + dep)
        visiting.remove(module); ordered[module] = path
    for root in binding['roots']: visit(root)
    require(set(ordered) == set(binding['modules']), 'Unreachable source')
    return ordered

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-project', required=True, type=Path)
    parser.add_argument('--lake', required=True, type=Path)
    parser.add_argument('--elan-home', type=Path)
    parser.add_argument('--output', required=True, type=Path, help='Fresh output directory; must not exist')
    parser.add_argument('--check-inputs-only', action='store_true')
    args = parser.parse_args()
    frozen, binding = verify_inputs()
    sources = ordered_sources(binding)
    dep = args.dependency_project.resolve()
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        require(sha(dep / name) == sha(HERE / 'dependency-project' / name), 'Dependency pin mismatch: ' + name)
    mathlib = next(p for p in load(dep / 'lake-manifest.json')['packages'] if p['name'] == 'mathlib')
    require(mathlib['rev'] == PIN, 'Mathlib manifest revision')
    revision = subprocess.check_output(['git','-C',str(dep / '.lake/packages/mathlib'),'rev-parse','HEAD'], text=True).strip()
    require(revision == PIN, 'Mathlib checkout revision')
    if args.check_inputs_only:
        print('PASS: package bindings and dependency pins'); return
    env = os.environ.copy()
    if args.elan_home: env['ELAN_HOME'] = str(args.elan_home.resolve())
    def query(*cmd):
        return subprocess.check_output([str(args.lake.absolute()), 'env', *cmd], cwd=dep, env=env, text=True).strip()
    lean = Path(query('which', 'lean')).resolve(); checker = lean.with_name('leanchecker')
    version = subprocess.check_output([str(lean), '--version'], env=env, text=True).strip()
    require('version 4.35.0,' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version, 'Compiler pin mismatch')
    package_root = (dep / '.lake/packages').resolve()
    paths = [(dep / p).resolve() for p in query('printenv','LEAN_PATH').split(os.pathsep)]
    dependencies = [str(p) for p in paths if package_root in p.parents and p.is_dir()]
    require(dependencies, 'No public dependency caches')
    out = args.output.resolve()
    require(not out.exists(), 'Output directory exists')
    require(out != HERE and not any(out == p or out in p.parents for p in sources.values()), 'Output overlaps inputs')
    out.mkdir(parents=True); root = out / '.build'; root.mkdir(); logs = out / 'logs'; logs.mkdir()
    env['LEAN_PATH'] = os.pathsep.join([str(root)] + dependencies)
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH','')
    report = {'passed': False, 'started_utc': now(), 'toolchain': version,
              'lean_sha256': sha(lean), 'checker_sha256': sha(checker),
              'input_manifest_sha256': sha(HERE / 'input-manifest.json'), 'mathlib_revision': revision,
              'lean_path': env['LEAN_PATH'], 'dependency_cache_boundary': 'Existing public dependency products reused; project products excluded.',
              'local_source_sha256': {m:sha(p) for m,p in sources.items()}, 'steps': []}
    def save(): (out / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    def run(label, command, negative=False):
        start = time.monotonic(); log = logs / (label + '.log')
        with log.open('w') as stream:
            proc = subprocess.run([str(x) for x in command], cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=600)
        result = log.read_text()
        ok = proc.returncode != 0 if negative else proc.returncode == 0
        if negative:
            ok = ok and 'error:' in result and 'False' in result and not any(s in result for s in ['unknown identifier','unknown constant','unknown module','object file','failed to synthesize'])
        report['steps'].append({'label': label, 'exit_code': proc.returncode, 'passed':ok, 'seconds':time.monotonic()-start, 'log_sha256':sha(log)})
        save(); print(label, proc.returncode, flush=True)
        require(ok, 'Failed step: ' + label)
        return result
    save()
    try:
        for module, path in sources.items():
            dst = root / (module.replace('.','/') + '.lean'); dst.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(path,dst)
            run('build-' + module, [lean, '--root=' + str(root), '-o', dst.with_suffix('.olean'), dst])
        audit = '\n'.join('import ' + m for m in binding['roots']) + '''
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[OWNED]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx.toNat]!
      if owned.contains mod then
        if info.isUnsafe then throwError "unsafe local declaration {n}"
        if info.isAxiom then throwError "local axiom {n}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError "unapproved axiom {ax} in {n}"
        logInfo m!"DECL|{mod}|{n}|{info.isTheorem}|{used}"
'''.replace('OWNED',','.join('`' + m for m in sources))
        (root / 'EnvironmentAudit.lean').write_text(audit)
        result = run('environment-audit', [lean, root / 'EnvironmentAudit.lean'])
        entries = re.findall(r'DECL\|([^|\n]+)\|([^|\n]+)\|', result)
        require({m for m,n in entries} == set(sources), 'Environment audit module coverage')
        require(len(entries) == len({n for m,n in entries}), 'Duplicate audit declarations')
        report['audited_declarations'] = len(entries)
        for module in binding['kernel_targets']:
            run('kernel-' + module, [checker, module, '-v'])
        for path in binding['negative_controls']:
            src = local(path); dst = root / src.name; shutil.copyfile(src,dst)
            run('negative-' + path.replace('/','_').removesuffix('.lean'), [lean,dst], negative=True)
        require(verify_inputs()[0] == frozen, 'Inputs changed during replay')
        require(all(sha(root / (m.replace('.','/')+'.lean')) == sha(p) for m,p in sources.items()), 'Build copy changed')
        for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
            require(sha(dep / name) == sha(HERE / 'dependency-project' / name), 'Pins changed during replay')
        report.update(passed=True, local_modules=len(sources), kernel_replays=len(binding['kernel_targets']),
                      negative_controls_rejected=len(binding['negative_controls']), inputs_preserved=True)
    except Exception as error:
        report['error'] = repr(error); raise
    finally:
        report['finished_utc'] = now(); save()
    print('PASS: ' + str(out / 'results.json'), flush=True)

if __name__ == '__main__': main()
