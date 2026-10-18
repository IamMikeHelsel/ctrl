#!/usr/bin/env python3
"""Fresh replay of interval-checker sources against the pinned, frozen dependencies.

No prebuilt checker or TerminalBase olean is imported. Each freshly built module is also passed
to leanchecker; the pinned toolchain and preexisting LeanControls/mathlib remain
the disclosed dependency trust boundary.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[2]
BASE = WORK / 'lean-controls'
MODULES = ['TerminalBase', 'IntervalChecker', 'CoefficientBounds', 'CoefficientCells',
           'TraceExecution', 'IntervalPilot', 'IntervalPilotActual', 'PilotSafety',
           'BetweenSample', 'PilotPath', 'FiniteHandoff', 'PilotContinuation', 'GeneralHandoff']
SOURCES = {m: (HERE.parent/'recovery-proof' if m=='TerminalBase' else HERE)/f'{m}.lean' for m in MODULES}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    env = os.environ.copy()
    local_lake = WORK / '.tools/elan/bin/lake'
    lake = os.environ.get('RECOVERY_LAKE') or (str(local_lake) if local_lake.exists() else shutil.which('lake'))
    if not lake:
        raise RuntimeError('Install Lean/elan or set RECOVERY_LAKE to the lake executable')
    if lake == str(local_lake):
        env['ELAN_HOME'] = str(WORK / '.tools/elan')
    def lake_read(*args):
        return subprocess.check_output([lake, 'env', *args], cwd=BASE, env=env,
                                       text=True).strip()
    lean = lake_read('which', 'lean')
    checker = str(Path(lean).with_name('leanchecker'))
    dependency_path = lake_read('printenv', 'LEAN_PATH')
    # lake reports dependency paths relative to its project working directory.
    dependency_path = ':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute()
                               else p for p in dependency_path.split(':'))
    hashes = {f'{m}.lean': digest(SOURCES[m]) for m in MODULES}
    report = {'scope': 'fresh checker, path and continuation modules plus recovery TerminalBase dependency; individual kernel replay; frozen base and pinned mathlib artifacts reused',
              'toolchain': lake_read('lean', '--version'),
              'source_sha256': hashes, 'verifier_sha256': digest(Path(__file__)),
              'mathlib_commit': subprocess.check_output(['git','-C',str(BASE/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),
              'steps': [], 'axioms': {}, 'passed': False}
    logdir = HERE/'verification-logs'
    logdir.mkdir(exist_ok=True)
    def run(label, cmd, cwd, env, expect=0):
        start=time.monotonic()
        with (logdir/f'{label}.log').open('w') as out:
            p=subprocess.run(cmd,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT)
        good = p.returncode == 0 if expect == 0 else p.returncode != 0
        report['steps'].append({'label':label,'exit_code':p.returncode,
                               'expected':'success' if expect==0 else 'rejection',
                               'passed':good,'command':cmd,'cwd':str(cwd),
                               'seconds':time.monotonic()-start,
                               'log_sha256':digest(logdir/f'{label}.log')})
        (HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
        print(label, p.returncode, f'{time.monotonic()-start:.2f}s', flush=True)
        if not good:
            raise RuntimeError(f'{label}: unexpected exit; inspect log')
    run('regenerate-coefficients',[os.sys.executable,str(HERE/'generate_coefficients.py'),'--check'],HERE,env)
    with tempfile.TemporaryDirectory(prefix='recovery-lean-') as temp:
        root = Path(temp)
        for m in MODULES:
            shutil.copy2(SOURCES[m],root/f'{m}.lean')
        checkenv=env.copy()
        checkenv['LEAN_PATH']=str(root)+':'+dependency_path
        checkenv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
        for m in MODULES:
            run('build-'+m,[lean,f'--root={root}','-o',str(root/f'{m}.olean'),str(root/f'{m}.lean')],root,checkenv)
        audits=['import '+m for m in MODULES]
        for m in MODULES:
            source=(root/f'{m}.lean').read_text()
            namespace=re.search(r'^namespace (\S+)',source,re.M).group(1)
            audits += ['#print axioms '+namespace+'.'+t for t in
                       re.findall(r'^theorem (\w+)',source,re.M)]
        (root/'Audit.lean').write_text('\n'.join(audits)+'\n')
        run('axiom-audit',[lean,str(root/'Audit.lean')],root,checkenv)
        audit=(logdir/'axiom-audit.log').read_text()
        for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",audit):
            names={x.strip() for x in axioms.split(',') if x.strip()}
            if not names <= ALLOWED:
                raise RuntimeError(f'Unexpected axioms for {name}: {names}')
            report['axioms'][name]=sorted(names)
        if len(report['axioms']) != len(audits)-len(MODULES):
            raise RuntimeError('Incomplete axiom audit')
        for m in MODULES:
            run('kernel-'+m,[checker,m,'-v'],root,checkenv)
        # A deliberately false terminal energy claim must fail at its interval proof.
        src=(root/'PilotSafety.lean').read_text()
        bad=src.replace('UncertainTravel.V z ≤ 12 := by', 'UncertainTravel.V z ≤ 0 := by', 1)
        bad=bad.replace('energy Generated.TravelQuarterLower.P z ≤ 12',
                        'energy Generated.TravelQuarterLower.P z ≤ 0', 1)
        if bad==src: raise RuntimeError('Mutation did not apply')
        (root/'FalseTerminalEnergy.lean').write_text(bad)
        run('reject-false-terminal-energy',[lean,str(root/'FalseTerminalEnergy.lean')],
            root,checkenv,expect=1)
    rejection=(logdir/'reject-false-terminal-energy.log').read_text()
    if 'FalseTerminalEnergy.lean:25:2: error: The proposition is provably false' not in rejection:
        raise RuntimeError('Mutation did not fail at the expected interval proof')
    report['false_terminal_energy_rejection'] = True
    report['source_unchanged'] = all(digest(SOURCES[m])==hashes[f'{m}.lean'] for m in MODULES)
    report['theorem_count']=len(report['axioms'])
    report['new_theorem_count']=sum(not n.startswith('LeanControls.RecoveryTerminal.') for n in report['axioms'])
    report['passed']=report['source_unchanged'] and all(s['passed'] for s in report['steps'])
    (HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':report['passed'],'theorem_count':report['theorem_count']}))

if __name__ == '__main__':
    main()
