#!/usr/bin/env python3
"""Replay translated witnesses in pinned upstream SOS, without solver discovery."""
from pathlib import Path
import hashlib,json,os,re,statistics,subprocess,sys,time
from datetime import datetime,timezone
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[1];repo=ROOT/'research/sos-comparison'
sys.path.insert(0,str(ROOT/'lean-controls/scripts'));from lean_runtime import runtime
lake,env=runtime(ROOT/'lean-controls');source=OUT/'TravelSOSReplay.lean'
copy=repo/'SOSTest/TravelSOSReplay.lean';meta=json.loads((OUT/'target-manifest.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source)==meta['source_sha256'] and source.read_bytes()==copy.read_bytes()
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
assert revision=='fb7ae417609093f04cf0608dc92e9343550c2ae4'
for case in meta['cases']:
 assert sha(ROOT/case['input'])==case['input_sha256']
 assert sha(ROOT/f"lean-controls/LeanControls/Generated/{case['name']}.lean")==case['main_generated_source_sha256']
expected={f"TravelSOSComparison.{c['name']}.{n}" for c in meta['cases'] for n in ['residual_nonnegative','residual_identity','interval_decrease']}
report={'status':'running','started_utc':datetime.now(timezone.utc).isoformat(),'upstream_revision':revision,
 'upstream_toolchain':(repo/'lean-toolchain').read_text().strip(),'upstream_manifest_sha256':sha(repo/'lake-manifest.json'),
 'target_manifest_sha256':sha(OUT/'target-manifest.json'),'source_sha256':sha(source),'source_bytes':source.stat().st_size,
 'witness_origin':meta['origin'],'scope':'four exact polynomial vertex residuals and decrease identities; no downstream saturation, exponential, clock or physical model proof in this comparison',
 'timing_boundary':'fresh Lean process via lake, imports and axiom queries; cached dependencies; no independent certificate search; different toolchain and theorem scope from main project',
 'runs':[]}
try:
 for k in range(1,4):
  command=[lake,'env','lean',str(copy),'--setup=.lake/build/ir/SOSTest/TravelSOSReplay.setup.json']
  start=time.perf_counter();r=subprocess.run(command,cwd=repo,env=env,capture_output=True,text=True,timeout=180)
  elapsed=time.perf_counter()-start;log=r.stdout+r.stderr;(OUT/f'replay-{k}.log').write_text(log)
  audits={n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
  assert r.returncode==0 and set(audits)==expected and all(set(a)<= {'propext','Classical.choice','Quot.sound'} for a in audits.values()),log[-500:]
  report['runs'].append({'elapsed_seconds':elapsed,'exit_code':r.returncode,'command':command,'working_directory':str(repo),'audit':audits,'log_sha256':sha(OUT/f'replay-{k}.log')})
  print(f'Replay {k}: {elapsed:.3f}s; all12declarations audited',flush=True)
 report['status']='verified';report['median_seconds']=statistics.median(r['elapsed_seconds'] for r in report['runs'])
except Exception as e:
 report['status']='failed';report['error']=str(e);raise
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat();(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
