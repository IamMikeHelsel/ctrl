#!/usr/bin/env python3
"""Compile frozen rational bindings and absolute-time composition against the fresh core."""
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
import verify

HERE = Path(__file__).resolve().parent
BINDINGS = HERE.parent / 'bindings'
ROOT = HERE / '.cache' / 'integration-build-v1'
LOGS = HERE / 'integration-logs'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def main():
    generic = json.loads((HERE / 'verification.json').read_text())
    assert generic['status'] == 'PASS', 'The generic fresh closure gate must pass first.'
    assert not ROOT.exists(), 'Do not overwrite an earlier integration run.'
    ROOT.mkdir(parents=True)
    LOGS.mkdir(exist_ok=True)
    binding_freeze = json.loads((BINDINGS / 'source-freeze.json').read_text())
    sources = {name[:-5]: BINDINGS / name for name in binding_freeze['sources']}
    for name in ['NativeCoverage', 'NativeGlobal']:
        sources[name] = HERE / (name + '.lean')
    for name, item in binding_freeze['sources'].items():
        assert sha(BINDINGS / name) == item['sha256']
    for name in ['coverage', 'global']:
        freeze = json.loads((HERE / (name + '-source-freeze.json')).read_text())
        assert sha(HERE / freeze['file']) == freeze['sha256']
    before = {m: {'path': str(p.relative_to(dev.WORK)), 'sha256': sha(p),
                  'bytes': p.stat().st_size} for m, p in sources.items()}
    env, lean, deps = dev.environment()
    env['LEAN_PATH'] = ':'.join([str(ROOT), str(verify.ROOT), deps])
    env['PATH'] = str(Path(lean).parent) + os.pathsep + env.get('PATH', '')
    checker = Path(lean).parent / 'leanchecker'
    result = {'status': 'RUNNING', 'started_at_utc': now(),
              'fresh_core_verification_sha256': sha(HERE / 'verification.json'),
              'bindings_source_freeze_sha256': sha(BINDINGS / 'source-freeze.json'),
              'coverage_source_freeze_sha256': sha(HERE / 'coverage-source-freeze.json'),
              'global_source_freeze_sha256': sha(HERE / 'global-source-freeze.json'),
              'sources': before, 'total_local_source_closure': len(generic['sources']) + len(sources),
              'builds': [], 'kernel_replays': []}

    def record():
        (HERE / 'integration-verification.json').write_text(json.dumps(result, indent=2) + '\n')

    def run(args, name, negative=False):
        started = time.monotonic()
        proc = subprocess.run(args, cwd=ROOT, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = LOGS / (name + '.log')
        log.write_text(proc.stdout)
        if negative:
            assert proc.returncode != 0 and 'error:' in proc.stdout
            assert not any(x in proc.stdout for x in ['unknown module prefix', 'object file',
                                                      'unknown constant', 'unknown identifier'])
        elif proc.returncode:
            print(proc.stdout[-16000:], flush=True)
            raise RuntimeError(name)
        return {'command': args, 'exit_code': proc.returncode,
                'seconds': round(time.monotonic() - started, 6),
                'log': str(log.relative_to(HERE)), 'log_sha256': sha(log)}

    try:
        for module, path in sources.items():
            forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',
                                   verify.strip_comments(path.read_text()))
            assert not forbidden, (module, forbidden)
            dst = ROOT / path.name
            shutil.copyfile(path, dst)
            print('BUILD', module, flush=True)
            e = run([lean, '--root=' + str(ROOT), '-o', str(dst.with_suffix('.olean')), str(dst)],
                    'build-' + module)
            result['builds'].append({'module': module, **e})
            record()
        modules = list(generic['sources']) + list(sources)
        audit = (HERE / 'EnvironmentAudit.lean').read_text()
        audit = audit.replace('import HandoffWitnesses',
                              'import HandoffWitnesses\nimport NativeInstances\nimport NativeGlobal')
        audit = re.sub(r'let owned : Array Name := #\[[^\n]*\]',
                       'let owned : Array Name := #[' + ','.join('`' + m for m in modules) + ']', audit)
        audit_path = HERE / 'IntegrationAudit.lean'
        audit_path.write_text(audit)
        shutil.copyfile(audit_path, ROOT / audit_path.name)
        result['environment_audit'] = run([lean, '--root=' + str(ROOT), str(ROOT / audit_path.name)],
                                           'environment-audit')
        result['audited_declaration_count'] = (LOGS / 'environment-audit.log').read_text().count('DECL|')
        for module in sources:
            print('KERNEL', module, flush=True)
            e = run([str(checker), module, '-v'], 'kernel-' + module)
            result['kernel_replays'].append({'module': module, **e})
            record()
        gap = '''import NativeCoverage
open NativeRational
def first : Piece := ⟨0,1,0,0,0,0⟩
def second : Piece := ⟨2,3,0,0,0,0⟩
example : check 3 [first,second] = true := by
  norm_num [check,chainOK,JoinOK,first,second]
'''
        gap_path = HERE / 'negative-controls' / 'GapAccepted.lean'
        gap_path.write_text(gap)
        shutil.copyfile(gap_path, ROOT / gap_path.name)
        result['clock_gap_negative_control'] = run([lean, '--root=' + str(ROOT), str(ROOT / gap_path.name)],
                                                    'negative-GapAccepted', negative=True)
        assert all(sha(path) == before[m]['sha256'] for m, path in sources.items())
        assert all(sha(dev.WORK / item['path']) == item['sha256']
                   for item in generic['sources'].values())
        result['source_preservation'] = 'PASS: all 43 local source modules match their checked hashes'
        result['status'] = 'PASS'
    except Exception as exc:
        result['status'] = 'FAIL'
        result['failure'] = repr(exc)
        raise
    finally:
        result['finished_at_utc'] = now()
        record()
    print(json.dumps({k: result[k] for k in ['status', 'total_local_source_closure',
                                           'audited_declaration_count', 'finished_at_utc']}, indent=2))


if __name__ == '__main__':
    main()
