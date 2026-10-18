#!/usr/bin/env python3
"""Rebuild the local proof closure and audit it without changing accepted files."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import dev

HERE = Path(__file__).resolve().parent
ROOT = HERE / '.cache' / 'verified-build-v2'
LOGS = HERE / 'verification-logs'
NEG = HERE / 'negative-controls'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def strip_comments(text):
    while '/-' in text:
        newer = re.sub(r'/-((?!/-|-/)[\s\S])*?-/', '', text)
        if newer == text:
            raise ValueError('Unclosed comment')
        text = newer
    return re.sub(r'--[^\n]*', '', text)


def main():
    assert not ROOT.exists(), 'Fresh verification root already exists; do not overwrite evidence.'
    ROOT.mkdir(parents=True)
    LOGS.mkdir(exist_ok=True)
    NEG.mkdir(exist_ok=True)
    env, lean, deps = dev.environment()
    env['LEAN_PATH'] = str(ROOT) + ':' + deps
    env['PATH'] = str(Path(lean).parent) + os.pathsep + env.get('PATH', '')
    checker = Path(lean).parent / 'leanchecker'
    sources = dev.source_closure('HandoffWitnesses')
    before = {m: {'path': str(p.relative_to(dev.WORK)), 'sha256': sha(p),
                  'bytes': p.stat().st_size} for m, p in sources.items()}
    result = {'started_at_utc': now(), 'status': 'RUNNING',
              'scope': 'Generic rounded handoff theorem and witnesses; sibling data bridge separate.',
              'fresh_local_source_modules': len(sources), 'sources': before,
              'source_freeze_sha256': sha(HERE / 'source-freeze.json'),
              'lean': {'path': lean, 'sha256': sha(Path(lean))},
              'leanchecker': {'path': str(checker), 'sha256': sha(checker)},
              'toolchain': {'text': (dev.BASE / 'lean-toolchain').read_text().strip(),
                            'sha256': sha(dev.BASE / 'lean-toolchain')},
              'lake_manifest_sha256': sha(dev.BASE / 'lake-manifest.json'),
              'builds': [], 'kernel_replays': [], 'negative_controls': []}
    (HERE / 'source-closure.json').write_text(json.dumps(before, indent=2) + '\n')

    def record():
        (HERE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')

    def run(args, log, expected=0):
        started = time.monotonic()
        proc = subprocess.run(args, cwd=ROOT, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log.write_text(proc.stdout)
        entry = {'command': args, 'exit_code': proc.returncode,
                 'seconds': round(time.monotonic() - started, 6),
                 'log': str(log.relative_to(HERE)), 'log_sha256': sha(log)}
        if expected == 0 and proc.returncode != 0:
            print(proc.stdout[-16000:], flush=True)
            raise RuntimeError(f'Command failed: {args}')
        if expected != 0:
            assert proc.returncode != 0, f'Negative control unexpectedly passed: {args}'
            assert 'error:' in proc.stdout and not any(x in proc.stdout for x in
                ['unknown module prefix', 'object file', 'unknown constant', 'unknown identifier']), proc.stdout
        return entry

    try:
        for m, p in sources.items():
            forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', strip_comments(p.read_text()))
            assert not forbidden, (m, forbidden)
            dst = ROOT / (m.replace('.', '/') + '.lean')
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
            print('BUILD', m, flush=True)
            e = run([lean, '--root=' + str(ROOT), '-o', str(dst.with_suffix('.olean')), str(dst)],
                    LOGS / ('build-' + m.replace('.', '_') + '.log'))
            result['builds'].append({'module': m, **e})
            record()
        result['source_scan'] = 'PASS: no sorry, admit, axiom, native_decide or unsafe in local code'

        audit = '''import HandoffWitnesses
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
'''.replace('OWNED', ','.join('`' + m for m in sources))
        audit_path = HERE / 'EnvironmentAudit.lean'
        audit_path.write_text(audit)
        shutil.copyfile(audit_path, ROOT / audit_path.name)
        result['environment_audit'] = run([lean, '--root=' + str(ROOT), str(ROOT / audit_path.name)],
                                            LOGS / 'environment-audit.log')
        result['audited_declaration_count'] = (LOGS / 'environment-audit.log').read_text().count('DECL|')

        for module in ['ScaledTracking', 'RoundedHandoff', 'HandoffWitnesses']:
            print('KERNEL', module, flush=True)
            e = run([str(checker), module, '-v'], LOGS / ('kernel-' + module + '.log'))
            result['kernel_replays'].append({'module': module, **e})

        source = (HERE / 'RoundedHandoff.lean').read_text()
        minus = 'coordinates 0 (scaledError σ f q h) i -\n'
        reserve = '∀ i, |coordinates 0 (scaledError σ g p 0) i| ≤ R+B := by'
        assert source.count(minus) == source.count(reserve) == 1
        mutants = {
            'WrongSign': source.replace(minus, minus.replace(' -', ' +')),
            'NoReserve': source.replace(reserve, reserve.replace('R+B', 'R')),
            'PositionOnly': '''import HandoffWitnesses
open LeanControls LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.HandoffWitnesses
example : |coordinates 0 (scaleState 10 (velocityOnly 0-rest 0)) 2| ≤ (0:ℝ) := by
  norm_num [velocityOnly,rest,coordinates,scaleState]
''',
            'PhysicalReset': '''import HandoffWitnesses
open LeanControls LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.HandoffWitnesses
example : |coordinates 0 (scaledError 10 unitPosition rest 0) 0| ≤ (0:ℝ) := by
  norm_num [unitPosition,rest,scaledError,error,coordinates,scaleState]
'''
        }
        for name, text in mutants.items():
            p = NEG / (name + '.lean')
            p.write_text(text)
            dst = ROOT / p.name
            shutil.copyfile(p, dst)
            print('NEGATIVE', name, flush=True)
            e = run([lean, '--root=' + str(ROOT), str(dst)], LOGS / ('negative-' + name + '.log'), 1)
            result['negative_controls'].append({'name': name, 'source_sha256': sha(p), **e})

        assert all(sha(sources[m]) == item['sha256'] for m, item in before.items())
        freeze = json.loads((HERE / 'source-freeze.json').read_text())
        assert all(sha(HERE / name) == item['sha256'] for name, item in freeze['files'].items())
        result['source_preservation'] = 'PASS: all 38 local sources and the source freeze are byte-identical'
        result['status'] = 'PASS'
    except Exception as exc:
        result['status'] = 'FAIL'
        result['failure'] = repr(exc)
        raise
    finally:
        result['finished_at_utc'] = now()
        record()
    print(json.dumps({k: result[k] for k in ['status', 'fresh_local_source_modules',
                                           'audited_declaration_count', 'finished_at_utc']}, indent=2))


if __name__ == '__main__':
    main()
