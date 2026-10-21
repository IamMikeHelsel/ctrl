#!/usr/bin/env python3
"""Run all project checks and bind the resulting evidence to source hashes."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time
from lean_runtime import runtime

PROJECT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes():
    files = [PROJECT/n for n in ['LeanControls.lean','Audit.lean','lean-toolchain',
             'lakefile.toml','lake-manifest.json','check.sh','requirements.txt']]
    for directory, pattern in [('LeanControls','*.lean'),('benchmarks','*.json'),('scripts','*.py')]:
        files.extend((PROJECT/directory).rglob(pattern))
    return {str(p.relative_to(PROJECT)):digest(p) for p in sorted(files)}


def main():
    output = PROJECT/'evidence/project-verification.json'
    output.parent.mkdir(exist_ok=True)
    lake, env = runtime(PROJECT)
    env['LAKE'] = lake
    initial = source_hashes()
    report = {'status':'running','started_utc':datetime.now(timezone.utc).isoformat(),
              'platform':platform.platform(),'python':sys.version,
              'lean_toolchain':(PROJECT/'lean-toolchain').read_text().strip(),
              'source_sha256':initial,'steps':[]}

    def save():
        output.write_text(json.dumps(report,indent=2)+'\n')

    save()
    try:
        steps = [('build-and-audit',['sh','check.sh']),
                 ('producer-tests',[sys.executable,'scripts/test_certificate_producer.py','--lean']),
                 ('model-bridge-tests',[sys.executable,'scripts/test_model_bridge.py']),
                 ('benchmark-verification',[sys.executable,'scripts/verify_benchmarks.py']),
                 ('uncertainty-artifact',[sys.executable,'scripts/verify_uncertainty_artifact.py'])]
        for label, command in steps:
            print(f'Checking {label}...',flush=True)
            start = time.monotonic()
            run = subprocess.run(command,cwd=PROJECT,env=env,capture_output=True,text=True,timeout=1200)
            log = output.parent/f'{label}.log'
            log.write_text(run.stdout+run.stderr)
            report['steps'].append({'label':label,'command':command,'exit_code':run.returncode,
                                    'seconds':time.monotonic()-start,
                                    'log':str(log.relative_to(PROJECT)),'log_sha256':digest(log)})
            save()
            if run.returncode:
                raise RuntimeError(f'{label} failed; inspect {log}')
        if source_hashes()!=initial:
            raise RuntimeError('Sources changed during verification. Review and rerun.')
        audits = json.loads((PROJECT/'evidence/axioms.json').read_text())
        report['audited_public_declarations'] = len(audits)
        report['allowed_axioms'] = ['Classical.choice','Quot.sound','propext']
        report['benchmark_manifest'] = 'evidence/benchmarks/verification.json'
        report['benchmark_manifest_sha256'] = digest(PROJECT/report['benchmark_manifest'])
        report['uncertainty_manifest'] = 'evidence/uncertainty-artifact/verification.json'
        report['uncertainty_manifest_sha256'] = digest(PROJECT/report['uncertainty_manifest'])
        report['status'] = 'verified'
    except Exception as exc:
        report['status'] = 'failed'
        report['error'] = str(exc)
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print(f"Verified {report['audited_public_declarations']} named public declarations; {output}")


if __name__ == '__main__':
    main()
