#!/usr/bin/env python3
"""Replay each local module separately from the already fresh compiled snapshot.
Preserves the killed combined replay; no original project oleans are used.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parent
CHECKPOINT=HERE/'full-bound-verification.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads(CHECKPOINT.read_text())
assert len(base['runs'])==23 and all(r['exit']==0 for r in base['runs'][:-1])
assert base['source_stable'] and base['completion_namespace_audited_declarations']==38
assert all(set(xs)<= {'propext','Classical.choice','Quot.sound'} for xs in base['axioms'].values())
replay=Path(base['fresh_directory'])
modules=list(base['sources_before'])
source_paths={m:Path(base['sources_origin'][m])for m in modules}
fresh_paths={m:replay/Path(m.replace('.','/')).with_suffix('.lean')for m in modules}
assert all(sha(source_paths[m])==base['sources_before'][m]==sha(fresh_paths[m])for m in modules)
olean_paths={m:replay/Path(m.replace('.','/')).with_suffix('.olean')for m in modules}
oleans_before={m:sha(p)for m,p in olean_paths.items()}
bin=Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0/bin'
env=os.environ.copy();env['LEAN_PATH']=base['lean_path'];env['PATH']=str(bin)+os.pathsep+env.get('PATH','')
result={**base,'passed':False,'method':'Fresh-source compilation checkpoint followed by one-module-per-process leanchecker replay of all 22 local modules.',
'compile_checkpoint':str(CHECKPOINT),'compile_checkpoint_sha256':sha(CHECKPOINT),
'combined_replay_attempt':base['runs'][-1],
'runs':base['runs'][:-1], 'sequential_replays':[], 'fresh_olean_hashes_before':oleans_before,
'signal_note':'Combined replay exited -9 (SIGKILL). Cause not established; no Lean proof error was reported. Retrying separately limits peak retained state.',
'max_rss_unit':'bytes on Darwin (/usr/bin/time -l)', 'runner_sha256':sha(Path(__file__))}
def save():
    result['sources_after']={m:sha(p)for m,p in source_paths.items()}
    result['source_stable']=result['sources_after']==base['sources_before']
    result['fresh_sources_stable']=all(sha(p)==base['sources_before'][m]for m,p in fresh_paths.items())
    result['fresh_olean_hashes_after']={m:sha(p)for m,p in olean_paths.items()}
    result['fresh_oleans_stable']=result['fresh_olean_hashes_after']==oleans_before
    (HERE/'full-bound-sequential-verification.json').write_text(json.dumps(result,indent=2)+'\n')
for m in modules:
    command=['/usr/bin/time','-l',str(bin/'leanchecker'),m,'-v']
    t=time.monotonic();p=subprocess.run(command,cwd=replay,env=env,text=True,capture_output=True)
    log='full-bound-sequential-'+m.replace('.','-')+'.log'
    (HERE/log).write_text(p.stdout+p.stderr)
    rss=re.search(r'(\d+)\s+maximum resident set size',p.stderr)
    record={'module':m,'command':command,'exit':p.returncode,'seconds':time.monotonic()-t,'log':log,'max_rss_bytes':int(rss.group(1))if rss else None}
    result['sequential_replays'].append(record);save()
    print(json.dumps(record),flush=True)
    if p.returncode:raise SystemExit('Replay failed: '+m)
result['kernel_replay_scope']='All 22 fresh local modules replayed separately into immutable fresh import environments. Cached pinned Mathlib dependencies trusted. Not a second independent prover.'
result['passed']=len(result['sequential_replays'])==22 and all(r['exit']==0 for r in result['sequential_replays']) and result['source_stable'] and result['fresh_sources_stable'] and result['fresh_oleans_stable']
result['successful_verification_seconds']=sum(r['seconds']for r in result['runs'])+sum(r['seconds']for r in result['sequential_replays'])
result['all_attempts_seconds']=result['successful_verification_seconds']+result['combined_replay_attempt']['seconds']
save()
print(json.dumps({'passed':result['passed'],'audited_completion_declarations':38,'modules_replayed':len(result['sequential_replays']),'successful_verification_seconds':result['successful_verification_seconds']}),flush=True)
raise SystemExit(0 if result['passed']else 1)
