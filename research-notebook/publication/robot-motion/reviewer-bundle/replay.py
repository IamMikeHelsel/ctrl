#!/usr/bin/env python3
"""Fresh replay of the frozen certificate. Python 3.9+, no Python dependencies."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
BUILDER_SHA = '740ebc266891b3f98b9ee567d19cced3c3ff187cbc091c08edfa52b276cd90fa'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(p):
    return json.loads(p.read_text())

def verify_inputs():
    manifest = load(HERE / 'input-manifest.json')
    for name, expected in manifest['files'].items():
        p = (HERE / name).resolve()
        require(HERE in p.parents, 'Invalid manifest path: ' + name)
        require(sha(p) == expected, 'Changed input: ' + name)
    return manifest

def fixture_checks():
    binding = load(HERE / 'fixture-binding.json')
    for filename, key in [('inputs/reference-checks.json', 'source_sha256'),
                          ('inputs/fixed-streams.json', 'streams_sha256'),
                          ('src/Fixtures.lean', 'output_sha256')]:
        require(sha(HERE / filename) == binding[key], 'Fixture input binding: ' + filename)
    def events(s):
        return [(Q(a), Q(d)) for a, d in re.findall(r'\(([-0-9/]+),([-0-9/]+)\)', s)]
    def jerk(h, es, t):
        return sum((d / h**3 * sum((-1)**i * comb(4, i) * max((t-a)/h-i, Q(0))
                                  for i in range(5)) for a, d in es), Q(0))
    def peak(h, es, c):
        points = {c} | {a+i*h for a, d in es for i in range(5) if a+i*h >= c}
        return max(abs(jerk(h, es, t)) for t in points)
    source = (HERE / 'src/Fixtures.lean').read_text()
    defs = {name: events(es) for name, es in re.findall(
        r'^def frozen_(\w+) : List QEvent := (\[.*\])$', source, re.M)}
    evals = {name: (Q(c), events(es), want == 'true') for name, c, es, want in re.findall(
        r'^#eval \("([^"]+_admission_\d+)", check \(1/5\) \(15/2\) \(([^)]+)\) (\[.*\]), (true|false)\)$', source, re.M)}
    require(len(defs) == 7 and len(evals) == 52, 'Fixture source counts')
    seen = set()
    rows = load(HERE / 'inputs/reference-checks.json')['cases']
    require(len(rows) == 7 and {r['case'] for r in rows} == set(defs), 'Fixture case coverage')
    for row in rows:
        case = row['case']
        saved = [(Q(e['time_s']), Q(e['delta_m'])) for e in row['accepted_events']]
        require(defs[case] == saved, 'Final history binding: ' + case)
        require(peak(Q(1,5), saved, Q(0)) == Q(row['exact_reference_jerk_peak_m_s3']), 'Final exact peak: ' + case)
        es, target = [], Q(0)
        for i, outcome in enumerate(row['outcomes']):
            if outcome['outcome'] not in ('accepted', 'jerk_rejected'):
                continue
            name = f'{case}_admission_{i}'
            c, actual, want = evals[name]
            require(c == Q(outcome['commit_s']), 'Admission time: ' + name)
            delta = Q(outcome['target_m']) - target
            candidate = es + ([(c, delta)] if delta else [])
            require(candidate == actual, 'Candidate history: ' + name)
            pk = peak(Q(1,5), candidate, c)
            ok = pk <= Q(15,2)
            require(want == ok == (outcome['outcome'] == 'accepted'), 'Admission outcome: ' + name)
            require(pk == Q(outcome['future_reference_jerk_peak_m_s3']), 'Exact candidate peak: ' + name)
            if ok:
                es, target = candidate, Q(outcome['target_m'])
            seen.add(name)
        require(es == saved, 'Reconstructed final history: ' + case)
    require(seen == set(evals), 'Unbound admission fixture')
    return {'final_histories': len(defs), 'admissions': len(seen), 'exact_fraction_replay': True}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-project', required=True, type=Path,
                        help='Already provisioned Lake project with the shipped exact pins and public dependency caches')
    parser.add_argument('--lake', required=True, type=Path, help='Pinned Lake executable or elan Lake shim')
    parser.add_argument('--elan-home', type=Path, help='Existing elan home, if not the default')
    parser.add_argument('--output', type=Path, help='New output directory; must not exist')
    args = parser.parse_args()
    frozen = verify_inputs()
    binding = load(HERE / 'source-bindings.json')
    original = load(HERE / 'provenance/accepted-builder-manifest.json')
    require(sha(HERE / 'provenance/accepted-builder-manifest.json') == BUILDER_SHA, 'Builder identity')
    require(binding['builder_manifest_sha256'] == BUILDER_SHA, 'Source binding identity')
    verification = load(HERE / 'provenance/original-verification.json')
    require(sha(HERE / 'provenance/original-verification.json') == original['files']['verification.json'], 'Original verification binding')
    for filename in ['contract.txt', 'theorem-map.json', 'fixture-binding.json']:
        require(sha(HERE / filename) == original['files'][filename], 'Original metadata: ' + filename)
    for p in (HERE / 'negative-controls').glob('*.lean'):
        require(sha(p) == original['files']['negative-controls/' + p.name], 'Original negative control: ' + p.name)
    inventory = binding['modules']
    require(set(inventory) == set(verification['source_paths']) == set(verification['source_sha256']), 'Original closure coverage')
    for module, info in inventory.items():
        require(info['path'] == 'src/' + module.replace('.', '/') + '.lean', 'Module path: ' + module)
        require(info['source_path'] == verification['source_paths'][module], 'Original source path: ' + module)
        require(sha(HERE / info['path']) == info['sha256'] == verification['source_sha256'][module], 'Original source hash: ' + module)
        if module in binding['package_modules']:
            require(info['sha256'] == original['files'][module + '.lean'], 'Package manifest binding: ' + module)
    sources, visiting = {}, set()
    def visit(module):
        if module in sources:
            return
        require(module not in visiting, 'Import cycle: ' + module)
        visiting.add(module)
        p = HERE / inventory[module]['path']
        for line in p.read_text().splitlines():
            line = line.removeprefix('public ')
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep in inventory:
                        visit(dep)
                    else:
                        require(dep.split('.')[0] in {'Mathlib','Lean','Init','Std','Batteries','Qq','Aesop'}, 'Unknown external import: ' + dep)
        sources[module] = p
        visiting.remove(module)
    visit('Composition')
    visit('Fixtures')
    require(set(sources) == set(inventory) and len(sources) == 44, 'Reachable source closure')
    exact_fixtures = fixture_checks()
    dep_project, lake = args.dependency_project.resolve(), args.lake.absolute()
    for filename in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']:
        require(sha(dep_project / filename) == sha(HERE / 'dependency-project' / filename), 'Dependency project pin mismatch: ' + filename)
    env = os.environ.copy()
    if args.elan_home:
        env['ELAN_HOME'] = str(args.elan_home.resolve())
    def query(*command):
        return subprocess.check_output([str(lake), 'env', *command], cwd=dep_project, env=env, text=True).strip()
    lean = Path(query('which', 'lean')).resolve()
    checker = lean.with_name('leanchecker')
    version = subprocess.check_output([str(lean), '--version'], env=env, text=True).strip()
    require('version 4.35.0,' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version, 'Lean version/commit mismatch')
    package_root = (dep_project / '.lake/packages').resolve()
    dep_paths, absent_dep_paths = [], []
    for part in query('printenv', 'LEAN_PATH').split(os.pathsep):
        p = (dep_project / part).resolve()
        if package_root in p.parents:
            if p.is_dir():
                dep_paths.append(str(p))
            else:
                absent_dep_paths.append(str(p))
    require(dep_paths, 'No external package caches found')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out = (args.output or HERE / 'verification' / stamp).resolve()
    require(not out.exists(), 'Output already exists: ' + str(out))
    require(out != HERE and not any(p == out or out in p.parents for p in sources.values()), 'Output overlaps sources')
    out.mkdir(parents=True)
    root, logs = out / '.build', out / 'logs'
    root.mkdir(); logs.mkdir()
    env['LEAN_PATH'] = os.pathsep.join([str(root)] + dep_paths)
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', '')
    report = {'passed': False, 'started_utc': datetime.now(timezone.utc).isoformat(),
              'builder_manifest_sha256': BUILDER_SHA, 'input_manifest_sha256': sha(HERE / 'input-manifest.json'),
              'toolchain': version, 'lean': str(lean), 'lean_sha256': sha(lean),
              'checker': str(checker), 'checker_sha256': sha(checker),
              'dependency_project': str(dep_project), 'lake_manifest_sha256': sha(dep_project / 'lake-manifest.json'),
              'mathlib_revision': verification['mathlib_pinned_revision'],
              'lean_path': env['LEAN_PATH'], 'absent_unused_dependency_paths': absent_dep_paths,
              'source_sha256': {m: sha(p) for m,p in sources.items()},
              'fixture_binding': exact_fixtures, 'steps': []}
    def save():
        (out / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    def run(label, command, negative=False):
        t = time.monotonic()
        log = logs / (label + '.log')
        with log.open('w') as stream:
            r = subprocess.run([str(x) for x in command], cwd=root, env=env,
                               stdout=stream, stderr=subprocess.STDOUT, timeout=600)
        ok = r.returncode != 0 if negative else r.returncode == 0
        report['steps'].append({'label': label, 'exit_code': r.returncode, 'passed': ok,
                                'seconds': time.monotonic()-t, 'log_sha256': sha(log)})
        save()
        print(label, r.returncode, flush=True)
        require(ok, 'Failed replay step: ' + label + '; see ' + str(log))
        return log.read_text()
    save()
    try:
        theorem_count, other_count, names = 0, 0, []
        for module, p in sources.items():
            dst = root / (module.replace('.', '/') + '.lean')
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
            s = re.sub(r'/-.*?-/|--[^\n]*', '', p.read_text(), flags=re.S)
            require(not re.search(r'\b(sorry|axiom|native_decide|unsafe)\b', s), 'Forbidden source token: ' + module)
            require(not re.search(r':=\s*by\s+admit\b|\n\s*admit\s*$', s), 'Admitted proof: ' + module)
            ns = re.findall(r'^namespace (\S+)', s, re.M)
            require(len(ns) == 1, 'Declaration scanner namespace: ' + module)
            theorems, others = [], []
            for line in s.splitlines():
                d = re.match(r'^\s*(.*?)\b(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s{(:]+)', line)
                if d and not re.search(r'\bprivate\b', d[1]):
                    (theorems if d[2] in ('lemma','theorem') else others).append(ns[0] + '.' + d[3])
            require(theorems == inventory[module]['public_theorems'] and others == inventory[module]['other_named_declarations'], 'Declaration inventory: ' + module)
            theorem_count += len(theorems); other_count += len(others); names += theorems + others
            run('build-' + module, [lean, '--root=' + str(root), '-o', dst.with_suffix('.olean'), dst])
        require(theorem_count == 660 and other_count == 332 and len(set(names)) == 992, 'Declaration counts')
        package_count = sum(len(inventory[m]['public_theorems']) for m in binding['package_modules'])
        require(package_count == 106 and theorem_count-package_count == 554, 'Package/inherited counts')
        for filename in ['NamedAudit.lean', 'EnvironmentAudit.lean']:
            shutil.copyfile(HERE / 'audit' / filename, root / filename)
        audit = run('named-axiom-audit', [lean, root / 'NamedAudit.lean'])
        axiom_names = set()
        for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", audit):
            used = {x.strip() for x in raw.split(',') if x.strip()}
            require(used <= ALLOWED_AXIOMS, 'Unapproved axioms: ' + name)
            axiom_names.add(name)
        axiom_names.update(re.findall(r"'([^']+)' does not depend on any axioms", audit))
        require(axiom_names == set(names), 'Named axiom audit coverage')
        audit = run('environment-audit', [lean, root / 'EnvironmentAudit.lean'])
        entries = re.findall(r'DECL\|([^|\n]+)\|([^|\n]+)\|', audit)
        require(len(entries) == 2996 and len({n for m,n in entries}) == 2996, 'Environment declaration count')
        require({m for m,n in entries} == set(sources), 'Environment module coverage')
        for module in ['ScaledTracking'] + binding['package_modules']:
            run('kernel-' + module, [checker, module, '-v'])
        for name in ['OmitCurrent','OmitInterior','EraseFuture','FalseUnitJerk']:
            dst = root / (name + '.lean')
            shutil.copyfile(HERE / 'negative-controls' / dst.name, dst)
            result = run('negative-' + name, [lean, dst], negative=True)
            require('error:' in result and ('decide' in result or 'kernel' in result), 'Wrong negative failure: ' + name)
            require(not any(s in result for s in ['unknown identifier','unknown module','object file']), 'Broken negative import: ' + name)
        fixture_log = (logs / 'build-Fixtures.log').read_text()
        finals = re.findall(r'\("(frozen_[^"]+)", (true|false)\)', fixture_log)
        admissions = re.findall(r'\("([^"]+_admission_\d+)", (true|false), (true|false)\)', fixture_log)
        require(len(finals) == 7 and all(x == 'true' for _,x in finals), 'Final fixture execution')
        require(len(admissions) == 52 and all(a == b for _,a,b in admissions), 'Admission fixture execution')
        require(verify_inputs() == frozen, 'Inputs changed during replay')
        for module,p in sources.items():
            require(sha(root / (module.replace('.', '/') + '.lean')) == sha(p), 'Build copy changed: ' + module)
        for filename in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
            require(sha(dep_project / filename) == sha(HERE / 'dependency-project' / filename), 'Pins changed during replay')
        report.update({'passed': True, 'local_modules':44, 'public_theorems':660,
                       'package_theorems':106, 'inherited_theorems':554,
                       'other_named_declarations':332, 'named_axiom_audits':992,
                       'environment_constants_audited':2996, 'kernel_replays':9,
                       'negative_controls_rejected':4, 'final_histories':7, 'evaluated_admissions':52,
                       'inputs_preserved':True, 'source_copies_match':True})
    except Exception as e:
        report['error'] = str(e)
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print('PASS: ' + str(out / 'results.json'), flush=True)

if __name__ == '__main__':
    main()
