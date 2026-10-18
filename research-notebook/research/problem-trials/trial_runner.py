#!/usr/bin/env python3
"""Bounded adapter harness; output is always an unverified diagnostic candidate.

The adapter receives the case JSON on stdin and an empty attempt directory via
TRIAL_OUTPUT_DIR. It must manage its model/checker loop within the stated budget.
Model-produced text is never executed by this runner. No provider is configured.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time
import uuid

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prepare(case_path):
    case_path = Path(case_path).resolve()
    case = json.loads(case_path.read_text())
    if not re.fullmatch(r'[a-zA-Z0-9][a-zA-Z0-9_.-]{0,100}',case['id']):
        raise ValueError('Invalid stable case id')
    if case.get('preparation_status') != 'ready':
        raise ValueError('Case is not prepared; pin its actual statement and current status first')
    if not case.get('source_inputs') or not case.get('statement_reviewed'):
        raise ValueError('A reviewed statement and hashed local inputs are required')
    for source in case['source_inputs']:
        path=(case_path.parent/source['path']).resolve()
        if not path.is_file() or sha(path)!=source['sha256']:
            raise ValueError('Prepared input is missing or changed: '+source['path'])
        if not source.get('source_url') and not source.get('local_fixture'):
            raise ValueError('Source provenance is required')
    return case

def run(case_path, adapter, output_root, seconds=300):
    if not 0 < seconds <= 300:
        raise ValueError('Active budget must be in (0,300] seconds')
    if not adapter or not all(isinstance(x,str) for x in adapter):
        raise ValueError('Adapter must be a nonempty JSON argv array')
    case=prepare(case_path)
    attempt=Path(output_root).resolve()/(case['id']+'-'+uuid.uuid4().hex[:12])
    attempt.mkdir(parents=True,exist_ok=False)
    input_bytes=Path(case_path).read_bytes()
    (attempt/'case.json').write_bytes(input_bytes)
    manifest={'case_id':case['id'],'started_utc':datetime.now(timezone.utc).isoformat(),
              'active_budget_seconds':seconds,'case_sha256':hashlib.sha256(input_bytes).hexdigest(),
              'adapter_argv_sha256':hashlib.sha256(json.dumps(adapter).encode()).hexdigest(),
              'execution_status':'running','mathematical_status':'unverified',
              'solved':False,'novelty_established':False,'publication_or_prize_claim':False}
    def save():
        temporary=attempt/'result.json.tmp'
        temporary.write_text(json.dumps(manifest,indent=2)+'\n')
        temporary.replace(attempt/'result.json')
    save()
    env=dict(os.environ)
    env['TRIAL_OUTPUT_DIR']=str(attempt)
    env['TRIAL_BUDGET_SECONDS']=str(seconds)
    start=time.monotonic()
    proc=None
    try:
        with (attempt/'stdout.txt').open('wb') as stdout, (attempt/'stderr.txt').open('wb') as stderr:
            proc=subprocess.Popen(adapter,stdin=subprocess.PIPE,stdout=stdout,stderr=stderr,
                                  cwd=Path(case_path).resolve().parent,env=env,start_new_session=True)
            try:
                proc.communicate(input=input_bytes,timeout=seconds)
                manifest['execution_status']='completed' if proc.returncode==0 else 'adapter_failed'
            except subprocess.TimeoutExpired:
                manifest['execution_status']='timed_out'
                os.killpg(proc.pid,signal.SIGKILL)
                proc.communicate()
            manifest['adapter_exit_code']=proc.returncode
    except BaseException as exc:
        if proc is not None and proc.poll() is None:
            os.killpg(proc.pid,signal.SIGKILL)
            proc.wait()
        manifest['execution_status']='runner_failed'
        manifest['error']=type(exc).__name__+': '+str(exc)
        raise
    finally:
        manifest['elapsed_seconds']=time.monotonic()-start
        manifest['finished_utc']=datetime.now(timezone.utc).isoformat()
        manifest['output_sha256']={p.name:sha(p) for p in [attempt/'stdout.txt',attempt/'stderr.txt'] if p.exists()}
        # Never promote a worker's self-reported 'proved' into an accepted result.
        manifest['mathematical_status']='unverified'
        manifest['solved']=False
        save()
    return manifest,attempt

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',type=Path,required=True)
    parser.add_argument('--adapter-argv',type=Path,required=True,
                        help='JSON argv array for an already configured adapter; no shell interpolation')
    parser.add_argument('--output-root',type=Path,default=Path(__file__).resolve().parent/'attempts')
    parser.add_argument('--seconds',type=float,default=300)
    args=parser.parse_args()
    result,path=run(args.case,json.loads(args.adapter_argv.read_text()),args.output_root,args.seconds)
    print(json.dumps({'attempt_directory':str(path),**result},indent=2))

if __name__ == '__main__':
    main()
