"""Fresh copied-source build, theorem axiom audit, leanchecker, false-square gate."""
from pathlib import Path
import hashlib, json, os, re, subprocess, tempfile, time
B = Path(__file__).resolve().parent
R = B.parents[4]
BASE = R / 'lean-controls'
FROZEN = R / 'research/weinstein-lean/operator-audit'
TARGETS = ['HodgeBridge', 'HodgeChecks', 'HodgeInterface']
DEPENDENCIES = ['GaugeSignAudit', 'ContractionCovariance']
EXPECTED = {
 'GaugeSignAudit': '31d7084df0a3e0a80373902c87c56be406c6a88c49d1262bf017fb320fcd34de',
 'ContractionCovariance': '663e101f90105aa6366fb37aec66ff175475fc348b977dcffc642ebf865cc083'}
env = os.environ.copy()
env['ELAN_HOME'] = str(R / '.tools/elan')
lake = str(R / '.tools/elan/bin/lake')
lean = subprocess.check_output([lake, 'env', 'which', 'lean'], cwd=BASE, env=env, text=True).strip()
paths = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=BASE, env=env, text=True).strip().split(':')
depaths = [str((BASE / p).resolve()) for p in paths]
env['PATH'] = str(Path(lean).parent) + ':' + env['PATH']
logs = B / 'logs'; logs.mkdir(exist_ok=True)
records = []
def execute(name, args, cwd, expected_failure=False):
    started = time.monotonic()
    with (logs / (name + '.log')).open('w') as out:
        p = subprocess.run(args, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT, timeout=300)
    rec = dict(step=name, command=args, exit_code=p.returncode, seconds=round(time.monotonic()-started,3))
    records.append(rec)
    print({k:v for k,v in rec.items() if k != 'command'}, flush=True)
    if expected_failure:
        assert p.returncode != 0, 'False square unexpectedly compiled'
    else:
        assert p.returncode == 0, (logs/(name+'.log')).read_text()[-8000:]
    return (logs/(name+'.log')).read_text()

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

sources = {m: (FROZEN if m in DEPENDENCIES else B)/(m+'.lean') for m in DEPENDENCIES+TARGETS}
hashes = {m:sha(p) for m,p in sources.items()}
assert all(hashes[m] == h for m,h in EXPECTED.items()), 'Frozen source changed before verification'
for m in TARGETS:
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', sources[m].read_text()), m
(B/'cache').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='hodge-fresh-', dir=B/'cache') as temp:
    tmp = Path(temp)
    env['LEAN_PATH'] = str(tmp) + ':' + ':'.join(depaths)
    for m,p in sources.items():
        (tmp/(m+'.lean')).write_bytes(p.read_bytes())
        assert sha(tmp/(m+'.lean')) == hashes[m]
        execute('fresh-'+m, [lean, '--root='+str(tmp), '-o', str(tmp/(m+'.olean')), str(tmp/(m+'.lean'))], tmp)
    names = []
    for m in TARGETS:
        names += ['GUHodgeBridge.'+n for n in re.findall(r'^theorem\s+(\w+)', sources[m].read_text(), re.M)]
    assert len(set(names)) == len(names)
    audit_source = '\n'.join('import '+m for m in TARGETS)+'\n'+ '\n'.join('#print axioms '+n for n in names)+'\n'
    (tmp/'Audit.lean').write_text(audit_source)
    (B/'Audit.lean.txt').write_text(audit_source)
    out = execute('axioms', [lean, str(tmp/'Audit.lean')], tmp)
    axioms = {n:[a.strip() for a in deps.split(',') if a.strip()] for n,deps in
      re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", out)}
    axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",out)})
    assert set(axioms) == set(names), (set(names)-set(axioms), set(axioms)-set(names))
    assert all(set(v) <= {'propext','Classical.choice','Quot.sound'} for v in axioms.values()), axioms
    for m in DEPENDENCIES+TARGETS:
        execute('kernel-'+m, [str(Path(lean).with_name('leanchecker')), m, '-v'], tmp)
    bad = '''import HodgeChecks
open GUHodgeBridge
-- Deliberately false, on the proved nonzero coordinate 2-form e_{0,1}.
example : H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) = e 2 I01 := by
  exact H_square (e 2 I01)
'''
    (B/'FalsePositiveSquare.lean.txt').write_text(bad)
    (tmp/'FalsePositiveSquare.lean').write_text(bad)
    failure = execute('false-positive-square', [lean, str(tmp/'FalsePositiveSquare.lean')], tmp, expected_failure=True)
    assert 'Type mismatch' in failure and 'H_square' in failure
    assert 'unknown module' not in failure.lower() and 'unknown identifier' not in failure.lower()
    assert all(sha(p) == hashes[m] for m,p in sources.items()), 'Source changed during verification'
    manifest = json.loads((BASE/'lake-manifest.json').read_text())
    revision = next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')
    report = dict(passed=True, source_sha256=hashes, theorem_count=len(names), axioms=axioms,
      steps=records, lean=subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
      mathlib_manifest_revision=revision, toolchain=(BASE/'lean-toolchain').read_text().strip(),
      frozen_sources_preserved=True, target_modules=TARGETS, dependency_modules=DEPENDENCIES,
      scope='Fresh copied sources and fresh target/dependency oleans in an isolated temporary directory. Pinned prebuilt Mathlib dependencies reused. All target theorem axioms audited. Five modules replayed with separate leanchecker. False +Id square rejected on proved nonzero e_{0,1}.')
    (B/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['passed','theorem_count','source_sha256','lean','mathlib_manifest_revision']},indent=2))
