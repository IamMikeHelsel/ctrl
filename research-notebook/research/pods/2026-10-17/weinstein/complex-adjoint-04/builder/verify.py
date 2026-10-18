"""Fresh sources, fresh target oleans, public declaration audits and kernel replay."""
from pathlib import Path
import hashlib, json, os, re, subprocess, tempfile, time

B = Path(__file__).resolve().parent
R = B.parents[5]
BASE = R/'lean-controls'
PREVIOUS = B.parent.parent/'clifford-contraction-03/builder'
DEPENDENCIES = ['CliffordModel', 'ContractionAlgebra', 'CliffordContraction', 'CliffordControls']
TARGETS = ['ComplexAdjoint', 'AdjointControls', 'ComplexContraction']
MODULES = DEPENDENCIES + TARGETS
PREFIX = {m: 'GUClifford' for m in DEPENDENCIES}
PREFIX['ContractionAlgebra'] = 'GUContraction'
PREFIX.update({m: 'GUComplex' for m in TARGETS})
env = os.environ.copy()
env['ELAN_HOME'] = str(R/'.tools/elan')
lake = str(R/'.tools/elan/bin/lake')
lean = subprocess.check_output([lake, 'env', 'which', 'lean'], cwd=BASE, env=env, text=True).strip()
paths = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=BASE, env=env, text=True).strip().split(':')
depaths = [str((BASE/p).resolve()) for p in paths]
env['PATH'] = str(Path(lean).parent)+':'+env['PATH']
logs = B/'logs'
logs.mkdir(exist_ok=True)
(B/'cache').mkdir(exist_ok=True)
records = []

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def frozen_state():
    result = {}
    for manifest in sorted(B.parent.parent.rglob('SHA256SUMS')):
        if B.parent in manifest.parents:
            continue
        result[str(manifest.relative_to(R))] = sha(manifest)
        for line in manifest.read_text().splitlines():
            digest, name = line.split('  ', 1)
            assert sha(manifest.parent/name) == digest, str(manifest.parent/name)
    return result

def run(name, args, cwd, expect_failure=False):
    start = time.monotonic()
    with (logs/(name+'.log')).open('w') as out:
        p = subprocess.run(args, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT, timeout=300)
    rec = {'step': name, 'command': args, 'exit_code': p.returncode,
           'seconds': round(time.monotonic()-start, 3)}
    records.append(rec)
    print({k: v for k, v in rec.items() if k != 'command'}, flush=True)
    output = (logs/(name+'.log')).read_text()
    assert (p.returncode != 0 if expect_failure else p.returncode == 0), output[-12000:]
    if expect_failure:
        assert any(x in output for x in ['unsolved goals', 'Type mismatch', 'Tactic `rewrite` failed']), output
        assert not any(x in output.lower() for x in ['unknown module', 'unknown identifier', 'file not found']), output
    return output

frozen_before = frozen_state()
sources = {m: (PREVIOUS if m in DEPENDENCIES else B)/(m+'.lean') for m in MODULES}
hashes = {m: sha(p) for m, p in sources.items()}
for m, p in sources.items():
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', p.read_text()), m

with tempfile.TemporaryDirectory(prefix='adjoint-fresh-', dir=B/'cache') as temp:
    tmp = Path(temp)
    env['LEAN_PATH'] = str(tmp)+':'+':'.join(depaths)
    for m, p in sources.items():
        (tmp/(m+'.lean')).write_bytes(p.read_bytes())
        assert sha(tmp/(m+'.lean')) == hashes[m]
        run('fresh-'+m, [lean, '--root='+str(tmp), '-o', str(tmp/(m+'.olean')), str(tmp/(m+'.lean'))], tmp)
    names = []
    target_names = []
    for m, p in sources.items():
        # Definitions and proof-carrying instances are audited along with theorems.
        pattern = r'^(?:theorem|lemma|def|abbrev|instance)\s+([^\s(:]+)'
        current = [PREFIX[m]+'.'+n for n in re.findall(pattern, p.read_text(), re.M)]
        names += current
        if m in TARGETS:
            target_names += current
    assert len(names) == len(set(names))
    audit = '\n'.join('import '+m for m in MODULES)+'\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
    (tmp/'Audit.lean').write_text(audit)
    (B/'Audit.lean.txt').write_text(audit)
    output = run('all-public-axioms', [lean, str(tmp/'Audit.lean')], tmp)
    axioms = {n: [a.strip() for a in deps.split(',') if a.strip()] for n, deps in
              re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output)}
    axioms.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", output)})
    assert set(axioms) == set(names), (set(names)-set(axioms), set(axioms)-set(names))
    assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in axioms.values()), axioms
    for m in MODULES:
        run('kernel-'+m, [str(Path(lean).with_name('leanchecker')), m, '-v'], tmp)

    client = '''import AdjointControls
import ComplexContraction
import CliffordControls
open GUComplex GUClifford GUContraction
open scoped TensorProduct
example : Function.Injective embed := embed_injective
example (z : ℂ) (a : Cl) : bar (z ⊗ₜ[ℝ] a) = star z ⊗ₜ[ℝ] star a := bar_tmul z a
example (a : CCl) : bar (Complex.I • a) = -Complex.I • bar a := bar_I_smul a
example (a b : CCl) : bar (a*b) = bar b * bar a := bar_mul a b
example (a : CCl) : bar (bar a) = a := bar_involutive a
example (a : Ix) : bar (cgamma a) = -cgamma a := bar_gamma a
example (a b : CCl) (ha : Skew a) (hb : Skew b) : Skew (a*b-b*a) := commutator_skew a b ha hb
example (a b : CCl) (ha : Skew a) (hb : Skew b) : Skew (Complex.I • (a*b+b*a)) := iAnti_skew a b ha hb
example : cgamma 7 * cgamma 7 = -1 := cgamma_seven_sq
example : iAnti (cgamma 0) (cgamma 0) ≠ 0 := iAnti_gamma_zero_ne_zero
example : fixedBar (iAnti (cgamma 0) (cgamma 0)) ≠ -iAnti (cgamma 0) (cgamma 0) := fixedBar_iAnti_not_skew
example : ¬ Skew (cgamma 0 * cgamma 0 + cgamma 0 * cgamma 0) := anticommutator_without_I_not_skew
example : bar (cgamma 0 * cgamma 7) ≠ bar (cgamma 0) * bar (cgamma 7) := bar_product_wrong_order_false
example (R : Tensor) (h : Curvature R) : complexK R = algebraMap ℝ CCl (-scal R) := complex_clifford_contraction R h
example : complexK sectional = algebraMap ℝ CCl (-2) := by
  rw [complex_clifford_contraction sectional sectional_curvature, sectional_scalar]
example : complexK fourform ≠ 0 := by
  rw [complexK_embed]
  intro h
  apply fourform_K_ne_zero
  apply embed_injective
  simpa only [map_zero] using h
'''
    (tmp/'Client.lean').write_text(client)
    (B/'Client.lean.txt').write_text(client)
    run('positive-client', [lean, str(tmp/'Client.lean')], tmp)

    original = sources['ComplexAdjoint'].read_text()
    mutations = {
      'WrongISignMutation': ('bar (Complex.I • a) = -Complex.I • bar a',
                            'bar (Complex.I • a) = Complex.I • bar a'),
      'WrongProductOrderMutation': ('bar (a*b) = bar b * bar a := star_mul a b',
                                   'bar (a*b) = bar a * bar b := star_mul a b'),
      'WithoutIMutation': ('def iAnti (a b : CCl) : CCl := Complex.I • (a*b+b*a)',
                          'def iAnti (a b : CCl) : CCl := a*b+b*a'),
    }
    for name, (before, after) in mutations.items():
        assert original.count(before) == 1
        changed = original.replace(before, after)
        (tmp/(name+'.lean')).write_text(changed)
        (B/(name+'.lean.txt')).write_text(changed)
        run(name, [lean, str(tmp/(name+'.lean'))], tmp, True)

    false_client = '''import AdjointControls
open GUComplex
example : fixedBar (iAnti (cgamma 0) (cgamma 0)) = -iAnti (cgamma 0) (cgamma 0) := by
  exact iAnti_skew (cgamma 0) (cgamma 0) (gamma_skew 0) (gamma_skew 0)
'''
    (tmp/'WrongAdjointClient.lean').write_text(false_client)
    (B/'WrongAdjointClient.lean.txt').write_text(false_client)
    run('WrongAdjointClient', [lean, str(tmp/'WrongAdjointClient.lean')], tmp, True)
    assert all(sha(p) == hashes[m] for m, p in sources.items())
    frozen_after = frozen_state()
    assert frozen_before == frozen_after
    manifest = json.loads((BASE/'lake-manifest.json').read_text())
    revision = next(x['rev'] for x in manifest['packages'] if x['name'] == 'mathlib')
    assert revision == '56a005855ea17e0b0958f73ec801ae140b0a1679'
    report = {
      'passed': True, 'target_modules': TARGETS, 'fresh_dependency_modules': DEPENDENCIES,
      'source_sha256': hashes, 'public_declarations_audited': names,
      'target_public_declarations_audited': target_names, 'axioms': axioms,
      'steps': records, 'frozen_manifests_preserved': frozen_after,
      'lean': subprocess.check_output([lean, '--version'], env=env, text=True).strip(),
      'toolchain': (BASE/'lean-toolchain').read_text().strip(),
      'mathlib_manifest_revision': revision,
      'scope': 'All seven target and accepted local dependency modules freshly copied and compiled. Pinned prebuilt Mathlib dependencies reused. Every public theorem, named instance, definition and abbreviation audited. All seven modules independently replayed by leanchecker. Positive client passed. Three semantic mutations and wrong-adjoint client rejected; direct counterexample theorems show why the changes are false.'
    }
    (B/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ['passed', 'source_sha256', 'lean', 'mathlib_manifest_revision']}, indent=2), flush=True)
