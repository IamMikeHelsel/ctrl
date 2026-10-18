#!/usr/bin/env python3
"""Replay the frozen 63-module proof closure. Requires Python 3.9+ and pinned Lean caches."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
GATE_HASHES = {'physical-arrival': '3abb293d650c12e90e1f36dc6296b0b81a2dbbe570692ed4ffdaaaa9f0dacf20', 'history-pruning': '854f736b05dd0a90608b75a6b89dc0230aaa7fa064f1461b62563808b8a5d288', 'successor-check': '006e5fee639c1eff6ce90d5e49945f2003ac47dc5155b7af8f4f265526ab856d', 'velocity': '025661f2f14bd9bdb3ef12ba49bdbd73d364c41971da1e749c50073a07e46023', 'fir-hold': '4036417f36ccf705244f9b285c8bdf4e98245d325c522a280ed8aeeed9ab2f00', 'future-commit': '13cd6d9eeaff3f0d930e5cc06adb0541a198162479396a11de4e45ade4c62e50'}
PIN = '56a005855ea17e0b0958f73ec801ae140b0a1679'
REVIEW_HASHES = {'physical-arrival': 'fbc7ba5ddeb97c92b788f670fa8c483708366c0c2bfdb7da246128d064df9470', 'history-pruning': '0fa33fc13c9593ff7cbee6bc3a25c4dd878508558b1d647c5bf9fdfecdd284b0', 'successor-check': '3620c6af12b074de71d19232ab07db61af2d4f4c191429bae000b23c45f92753', 'velocity': '101a0b071b2c05bf1b0dbac407b1b43f7319b7b7887180941d295c7ff35fac16', 'fir-hold': '3fbe0730f46abcec1025548b3b254f4618554004a014962c10d32dd0773bac56', 'future-commit': 'bdb93bf80225dd84b4cc927a571a8e93587b5ab248c9657e16449b15c7b850d9'}
PIN_FILE_HASHES = {'lean-toolchain': 'ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c', 'lakefile.toml': '11e66dd0e006225492ddda5d1dc30cd9550b207b25fc6cd4f0f5a6f8e432c00d', 'lake-manifest.json': '6525e7195148f78782a5aeeee8f1a8a90eebc4ecd4e9c3cdc215b29ddd3fbcb0'}
EXPECTED_ROOTS = ['PhysicalArrival', 'HistoryPruning', 'SuccessorGuard', 'VelocityOracle', 'FIRHoldWitness', 'FutureCommitFixtures']
EXPECTED_KERNEL_TARGETS = ['Composition', 'ScaledTracking', 'AccelerationGuard', 'AccelerationFixtures', 'ReversalProposal', 'TimedAdmission', 'PhysicalArrival', 'HistoryPruning', 'SuccessorGuard', 'VelocityBernstein', 'VelocityGuard', 'VelocityAdmission', 'VelocityFixtures', 'VelocityOracle', 'Settling', 'SettlingFixtures', 'QuadraticAlgebra', 'QuadraticTrajectory', 'FIRHold', 'FIRHoldWitness', 'FutureCommit', 'FutureCommitFixtures']
EXPECTED_NEGATIVE_CONTROLS = {'negative-controls/physical-arrival/FalseExactArrivalFromBand.lean': {'gate': 'physical-arrival', 'original_path': 'negative-controls-02/FalseExactArrivalFromBand.lean', 'sha256': '23a333d4a4225a4bd56ba7b4e38eeffc59337ec8e0e28da9352df4624d3910b9'}, 'negative-controls/physical-arrival/FalseTightSelection.lean': {'gate': 'physical-arrival', 'original_path': 'negative-controls-02/FalseTightSelection.lean', 'sha256': 'fce222e93c9759194a6eb178e1eca331bc6f1219bbc6447d549b7177a443f566'}, 'negative-controls/physical-arrival/FalseTighterBudget.lean': {'gate': 'physical-arrival', 'original_path': 'negative-controls-02/FalseTighterBudget.lean', 'sha256': '903857368acc927e1c435b98bb48710c7d27606c9625bdfa72c6aca68df6ce90'}, 'negative-controls/physical-arrival/FalseZeroProgress.lean': {'gate': 'physical-arrival', 'original_path': 'negative-controls-02/FalseZeroProgress.lean', 'sha256': '49d5837e201808212dc7f1e8e04201c03b14833ec9f1a543b7b2202a8a3f9f53'}, 'negative-controls/history-pruning/FalsePositionOffset.lean': {'gate': 'history-pruning', 'original_path': 'negative-controls/FalsePositionOffset.lean', 'sha256': '8f2eab8f51e5e567ad3a40140be34539ce4e1ed507c3a21b8254d6f7dc0c5ae5'}, 'negative-controls/history-pruning/FalsePrematureRemoval.lean': {'gate': 'history-pruning', 'original_path': 'negative-controls/FalsePrematureRemoval.lean', 'sha256': '65d54951f04c08e640939ed8cad9ddee25c6bd0176dc99f27c26076ac8487be8'}, 'negative-controls/history-pruning/FalseQueuedRemoval.lean': {'gate': 'history-pruning', 'original_path': 'negative-controls/FalseQueuedRemoval.lean', 'sha256': '0c1cd81a3f9a478ecbc56c54d2ef02bde1c925d91c17409bb78ad95fbe50ab6d'}, 'negative-controls/history-pruning/FalseUnsignedOffset.lean': {'gate': 'history-pruning', 'original_path': 'negative-controls/FalseUnsignedOffset.lean', 'sha256': '5ed6348b855a3e30f0a4d9bc589a2d0aeef56196ae98fa6ffaac8b338a92a4d6'}, 'negative-controls/successor-check/FalseCurrentAcceptance.lean': {'gate': 'successor-check', 'original_path': 'negative-controls/FalseCurrentAcceptance.lean', 'sha256': 'f5459034ad385e5d95c576d2f4b2284b2efcf29af0e27647b983b204e3eece0e'}, 'negative-controls/successor-check/FalseInteriorAcceptance.lean': {'gate': 'successor-check', 'original_path': 'negative-controls/FalseInteriorAcceptance.lean', 'sha256': 'e2650b5a686c5de6c2fc7badf2b5078316983cbe04ca2a9cce38f37f371e64bc'}, 'negative-controls/successor-check/FalseQueuedAcceptance.lean': {'gate': 'successor-check', 'original_path': 'negative-controls/FalseQueuedAcceptance.lean', 'sha256': '051e90c12269299cd81ef6b9b08295c43ff832b61b02b521455902efb750ed26'}, 'negative-controls/successor-check/FalseSuccessor.lean': {'gate': 'successor-check', 'original_path': 'negative-controls/FalseSuccessor.lean', 'sha256': 'db2f933137fe6c1f6066dd64c88e8743cb52c803d6518eb68c688c4811291cd2'}, 'negative-controls/velocity/FalseConservativeAcceptance.lean': {'gate': 'velocity', 'original_path': 'negative-controls/FalseConservativeAcceptance.lean', 'sha256': 'd606638c2eebd553ea2e4bbd051bc84a7179dc7dff50add90d198b9e2d0005bf'}, 'negative-controls/velocity/FalseCurrentAcceptance.lean': {'gate': 'velocity', 'original_path': 'negative-controls/FalseCurrentAcceptance.lean', 'sha256': 'b04d6d62ed9742cc144d3be8505ebbfd4ce9bf5e255610c789320bbf618e39e2'}, 'negative-controls/velocity/FalseEndpointSufficiency.lean': {'gate': 'velocity', 'original_path': 'negative-controls/FalseEndpointSufficiency.lean', 'sha256': 'eb46a239229113df966fc7cc062a181741e3224a14024bc6ca4b88c6711f7962'}, 'negative-controls/velocity/FalseNoSafeRejectedHistory.lean': {'gate': 'velocity', 'original_path': 'negative-repair-01/FalseNoSafeRejectedHistory.lean', 'sha256': 'f0444952835cda1ede9022e1c6223121d72da9a30138c4e22914d69e196d2182'}, 'negative-controls/velocity/FalseQueuedAcceptance.lean': {'gate': 'velocity', 'original_path': 'negative-controls/FalseQueuedAcceptance.lean', 'sha256': '542b3bb4254c9b9fa97f5aed8941e5d469684d607847ccc9d11a707894f44dae'}, 'negative-controls/velocity/FalseTightDeadlineSelection.lean': {'gate': 'velocity', 'original_path': 'negative-controls/FalseTightDeadlineSelection.lean', 'sha256': 'dc74bb0babdf63e6b5382389843239c3514e53d0f8e4037ebe6f8c4f1d3f45ad'}, 'negative-controls/fir-hold/drop-wait-before-speed-band.lean': {'gate': 'fir-hold', 'original_path': 'negative-controls/drop-wait-before-speed-band.lean', 'sha256': '5aecf135e43e267918b9cb207fbdad63600794aa9961d0611ea8aa01b6d84116'}, 'negative-controls/fir-hold/erase-inherited-state.lean': {'gate': 'fir-hold', 'original_path': 'negative-controls/erase-inherited-state.lean', 'sha256': '06ca9ca7bf0a735fc34eb66aebcda7d16a462ccb59b11df8ce58a6cd6f686f40'}, 'negative-controls/fir-hold/erase-initial-error.lean': {'gate': 'fir-hold', 'original_path': 'negative-controls/erase-initial-error.lean', 'sha256': 'b74d42775b41a6273cb395b7eba2cd1120033bdc43bc9e13ef5825d030b06a0c'}, 'negative-controls/fir-hold/exact-physical-arrival.lean': {'gate': 'fir-hold', 'original_path': 'negative-controls/exact-physical-arrival.lean', 'sha256': 'bf87cd9fb307d8bfa145009f948f3a2968e4d21338b542c19d4cd721a7f806e6'}, 'negative-controls/fir-hold/unshifted-physical-inputs.lean': {'gate': 'fir-hold', 'original_path': 'negative-controls/unshifted-physical-inputs.lean', 'sha256': '713464b17d943115b3d93994263702eae50399df6e309950036e5e6beb3f04ee'}, 'negative-controls/fir-hold/wrong-reference-clock.lean': {'gate': 'fir-hold', 'original_path': 'negative-controls/wrong-reference-clock.lean', 'sha256': 'cbe8fa2d0e2026d197d2e54f421965ef164199c09f6a7babb60a0e72c451143b'}, 'negative-controls/future-commit/FalseDelayedCommitAcceptance.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseDelayedCommitAcceptance.lean', 'sha256': '9aab64b6826349be53705636274c4e53bd2b967287161d2d7182ec6941b37f69'}, 'negative-controls/future-commit/FalseDuplicateGoal.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseDuplicateGoal.lean', 'sha256': '2541978d3576e6c51845b3e918a71fd45cf2e3e4e55c2a29f32862b54d02a6de'}, 'negative-controls/future-commit/FalseLateAcceptance.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseLateAcceptance.lean', 'sha256': '666b85c23982e0a0a2f56e695ac23f4e8ccd0e874d7b38311868da54a78e2674'}, 'negative-controls/future-commit/FalseLatePrefix.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseLatePrefix.lean', 'sha256': '8038d539882c1d8d1fb7edf79e95f61f38a3c66344ba9f07c9eb9e6e43091c43'}, 'negative-controls/future-commit/FalseReusedHistoryVersion.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseReusedHistoryVersion.lean', 'sha256': '035d9341176c9264c806ce19f45facfeb5235bb7d9d44416c34b2f6e0eec5f88'}, 'negative-controls/future-commit/FalseReusedTaskVersion.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseReusedTaskVersion.lean', 'sha256': 'a0d2dbf21b744ac2fbf23c46845fe59b1c57cd6ee5588118eeaecc2f927de228'}, 'negative-controls/future-commit/FalseStaleHistoryGoal.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseStaleHistoryGoal.lean', 'sha256': 'e02df67a30c8bf5ff4fcf177e5a85237ed80aa7f81bd13b1634c52c288a6d727'}, 'negative-controls/future-commit/FalseSupersededGoal.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseSupersededGoal.lean', 'sha256': '293bb87eb54ff3f1664b36ca2e5a78fc3c238ab165b7c4eae7fe923105761f5b'}, 'negative-controls/future-commit/FalseTightAcceptance.lean': {'gate': 'future-commit', 'original_path': 'negative-controls/FalseTightAcceptance.lean', 'sha256': '190dff753ab8621750e81209759150da05ac0ffdc21d3cff1cf5787d05c64ead'}}
EXPECTED_BINDINGS_SHA256 = '2cf42893246b472647a232af95ec48f6d618cf945f57ee2c0370e8aaae0b5149'
EXPECTED_REVIEW_BINDINGS_SHA256 = '29ad08e3cab25cca4ad8c1c55bd259d00682e06464384d7fe1ccb4f152889d29'
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
    for name, digest in PIN_FILE_HASHES.items():
        require(sha(HERE / 'dependency-project' / name) == digest, 'Canonical dependency pin: ' + name)
    require(sha(HERE / 'source-bindings.json') == EXPECTED_BINDINGS_SHA256, 'Source binding plan')
    require(sha(HERE / 'review-bindings.json') == EXPECTED_REVIEW_BINDINGS_SHA256, 'Review binding plan')
    require(binding['roots'] == EXPECTED_ROOTS, 'Root plan')
    require(binding['kernel_targets'] == EXPECTED_KERNEL_TARGETS, 'Kernel replay plan')
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
    require(set(union) == set(binding['modules']) and len(union) == 63, 'Module coverage')
    for module, info in binding['modules'].items():
        require(info['path'] == 'src/' + module.replace('.', '/') + '.lean', 'Module path: ' + module)
        require(info['original_path'] == union[module]['path'], 'Original source path: ' + module)
        require(sha(local(info['path'])) == info['sha256'] == union[module]['sha256'], 'Original source hash: ' + module)
    require(binding['negative_controls'] == EXPECTED_NEGATIVE_CONTROLS, 'Negative control plan')
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
    require(out != HERE and HERE not in out.parents and not any(out == p or out in p.parents for p in sources.values()), 'Output overlaps inputs')
    out.mkdir(parents=True); root = out / '.build'; root.mkdir(); logs = out / 'logs'; logs.mkdir()
    env['LEAN_PATH'] = os.pathsep.join([str(root)] + dependencies)
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH','')
    report = {'passed': False, 'started_utc': now(), 'toolchain': version,
              'lean_executable': str(lean), 'checker_executable': str(checker), 'lean_sha256': sha(lean), 'checker_sha256': sha(checker),
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
        report['compiled_objects'] = {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob('*')) if p.is_file() and '.olean' in p.name}
        report['compiled_module_names'] = list(sources)
        report.update(passed=True, local_modules=len(sources), kernel_replays=len(binding['kernel_targets']),
                      negative_controls_rejected=len(binding['negative_controls']), inputs_preserved=True)
    except Exception as error:
        report['error'] = repr(error); raise
    finally:
        report['finished_utc'] = now(); save()
    print('PASS: ' + str(out / 'results.json'), flush=True)

if __name__ == '__main__': main()
