"""Fresh source compilation, axiom audit, kernel replay, and a false-defect check."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time
TARGET = Path(__file__).resolve().parent
ROOT = TARGET.parents[2]
BASE = ROOT / 'lean-controls'
MODULES = ['GaugeSignAudit', 'ContractionCovariance']
env = os.environ.copy()
env['ELAN_HOME'] = str(ROOT / '.tools/elan')
lake = str(ROOT / '.tools/elan/bin/lake')
lean = subprocess.check_output([lake, 'env', 'which', 'lean'], cwd=BASE, env=env, text=True).strip()
leanpath = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=BASE, env=env, text=True).strip()
depaths = [str((BASE / p).resolve()) if not Path(p).is_absolute() else p for p in leanpath.split(':')]
env['PATH'] = str(Path(lean).parent) + ':' + env['PATH']
logs = TARGET / 'logs'
logs.mkdir(exist_ok=True)
records = []
def execute(name, args, cwd, expected=0):
    start = time.monotonic()
    with (logs / (name + '.log')).open('w') as out:
        p = subprocess.run(args, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT)
    record = {'step': name, 'exit_code': p.returncode, 'seconds': round(time.monotonic()-start, 3)}
    records.append(record)
    print(record, flush=True)
    if expected == 0 and p.returncode != 0:
        raise RuntimeError((logs / (name+'.log')).read_text()[-8000:])
    if expected != 0 and p.returncode == 0:
        raise RuntimeError('False statement unexpectedly compiled')
    return (logs / (name+'.log')).read_text()

with tempfile.TemporaryDirectory(prefix='gu-operator-') as tmpname:
    tmp = Path(tmpname)
    env['LEAN_PATH'] = str(tmp) + ':' + ':'.join(depaths)
    names = []
    hashes = {}
    for module in MODULES:
        source = (TARGET / (module + '.lean')).read_text()
        hashes[module] = hashlib.sha256(source.encode()).hexdigest()
        names += re.findall(r'^(?:@\[[^\]]+\]\s+)?theorem (\w+)', source, re.M)
        (tmp / (module+'.lean')).write_text(source)
        execute('build-'+module, [lean, '--root='+str(tmp), '-o', str(tmp/(module+'.olean')), str(tmp/(module+'.lean'))], tmp)
    (tmp / 'Audit.lean').write_text('\n'.join('import '+m for m in MODULES)+'\n'+
        '\n'.join('#print axioms GUOperatorAudit.'+n for n in names)+'\n')
    audit = execute('axioms', [lean, str(tmp/'Audit.lean')], tmp)
    axioms = {n:[a.strip() for a in deps.split(',') if a.strip()] for n,deps in
        re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", audit)}
    axioms.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", audit)})
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert len(axioms) == len(names), (len(axioms), len(names))
    assert all(set(v) <= allowed for v in axioms.values())
    for module in MODULES:
        execute('kernel-'+module, [str(Path(lean).with_name('leanchecker')), module, '-v'], tmp)
    bad = (tmp/'GaugeSignAudit.lean').read_text().replace(
        'conjugate h (torsionMinus A e w) - (shift A h + shift A h)',
        'conjugate h (torsionMinus A e w) - shift A h', 1)
    assert bad != (tmp/'GaugeSignAudit.lean').read_text()
    (tmp/'BadDefect.lean').write_text(bad)
    mutation = execute('false-defect', [lean, str(tmp/'BadDefect.lean')], tmp, expected=1)
    assert 'unsolved goals' in mutation
    assert 'unknown module' not in mutation.lower()
    for module in MODULES:
        assert hashlib.sha256((TARGET/(module+'.lean')).read_bytes()).hexdigest() == hashes[module]
    report = {'passed': True, 'theorem_count': len(names), 'source_sha256': hashes,
        'axioms': axioms, 'steps': records,
        'lean': subprocess.check_output([lean, '--version'], env=env, text=True).strip(),
        'mathlib_commit': subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),
        'scope': 'Fresh temporary source copies and fresh target oleans. All public theorem axioms checked. Every target replayed by leanchecker. Pinned prebuilt dependencies reused. False factor-of-two defect rejected.'}
    (TARGET/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
