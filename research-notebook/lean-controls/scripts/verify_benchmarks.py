#!/usr/bin/env python3
"""Regenerate, freshly typecheck, and axiom-audit each exact certificate.

A verification manifest binds success to the input and generated source hashes.
It is evidence of this run, not a proof of model-to-physics correspondence.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from generate_interval_certificate import produce
from lean_runtime import runtime

PROJECT=Path(__file__).resolve().parents[1]
WORKSPACE=PROJECT.parent
CASES=[('double-integrator','DoubleIntegrator'),('double-integrator-wide','DoubleIntegratorWide'),
       ('jerk-integrator','JerkIntegrator'),('coupled-planar','CoupledPlanar'),
       ('actuator-lag-lower','LagLower'),('actuator-lag-upper','LagUpper'),
       ('travel-quarter-lower','TravelQuarterLower'),('travel-quarter-upper','TravelQuarterUpper'),
       ('travel-full-lower','TravelFullLower'),('travel-full-upper','TravelFullUpper')]
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(blob): return hashlib.sha256(blob).hexdigest()

def main():
    out=PROJECT/'evidence/benchmarks';out.mkdir(parents=True,exist_ok=True)
    manifest={'started_utc':datetime.now(timezone.utc).isoformat(),'status':'running',
              'lean_toolchain':(PROJECT/'lean-toolchain').read_text().strip(),
              'mathlib_revision':next(p['rev'] for p in json.loads((PROJECT/'lake-manifest.json').read_text())['packages'] if p['name']=='mathlib'),
              'producer_sha256':digest(Path(__file__).with_name('generate_interval_certificate.py').read_bytes()),
              'cases':[]}
    path=out/'verification.json'
    def save(): path.write_text(json.dumps(manifest,indent=2)+'\n')
    save()
    lake, env = runtime(PROJECT)
    try:
        for slug,name in CASES:
            model=PROJECT/f'benchmarks/{slug}.json'
            source,witness=produce(json.loads(model.read_text()),name)
            target=PROJECT/f'LeanControls/Generated/{name}.lean'
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_text(source)
            target.with_suffix('.certificate.json').write_text(json.dumps(witness,indent=2)+'\n')
            declarations=[f'LeanControls.Generated.{name}.{d}' for d in re.findall(r'^theorem (\w+)',source,re.M)]
            audit='\n'.join('#print axioms '+d for d in declarations)+'\n'
            start=time.monotonic()
            with tempfile.TemporaryDirectory(prefix='lean-benchmark-') as directory:
                check=Path(directory)/f'{name}.lean';check.write_text(source+'\n'+audit)
                command=[lake,'env','lean',str(check)]
                result=subprocess.run(command,cwd=PROJECT,env=env,
                    capture_output=True,text=True,timeout=300)
            elapsed=time.monotonic()-start
            log=result.stdout+result.stderr
            (out/f'{slug}.log').write_text(log)
            if result.returncode:
                raise RuntimeError(f'{slug}: Lean rejected generated source; inspect {slug}.log')
            records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
            empty=re.findall(r"'([^']+)' does not depend on any axioms",log)
            axioms={n:sorted({a.strip() for a in ax.split(',') if a.strip()}) for n,ax in records}
            axioms.update({n:[] for n in empty})
            if set(axioms)!=set(declarations) or any(not set(ax)<=ALLOWED for ax in axioms.values()):
                raise RuntimeError(f'{slug}: missing audit output or unexpected axiom')
            if digest(target.read_bytes())!=digest(source.encode()):
                raise RuntimeError(f'{slug}: generated file changed during verification')
            manifest['cases'].append({'name':name,'status':'verified','input':str(model.relative_to(PROJECT)),
                'role':('polynomial gain/exponential enclosure vertex for SaturatedLag' if name.startswith('Travel')
                        else 'polynomial enclosure vertex for ActuatorLag' if name.startswith('Lag')
                        else 'exact nominal polynomial transition'),
                'input_bytes_sha256':digest(model.read_bytes()),'source':str(target.relative_to(PROJECT)),
                'source_sha256':digest(source.encode()),'source_bytes':len(source.encode()),
                'dimension':witness['dimension'],'degree':witness['degree'],'partition':witness['partition'],
                'decay_margin':witness['decay_margin'],'energy_lower':witness['energy_lower'],
                'energy_upper':witness['energy_upper'],'seconds':elapsed,'lean_exit_code':result.returncode,
                'command':command,'working_directory':str(PROJECT),
                'checked_source_sha256':digest((source+'\n'+audit).encode()),
                'audit':axioms})
            save()
            print(f'{name}: verified {len(declarations)} declarations in {elapsed:.2f}s',flush=True)
        manifest['status']='verified'
    except Exception as exc:
        manifest['status']='failed';manifest['error']=str(exc);save()
        raise
    finally:
        manifest['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print(path)

if __name__=='__main__': main()
