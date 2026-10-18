#!/usr/bin/env python3
"""Fresh-source replay of the isolated completion spike; no controls .olean files."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
BRIDGE=HERE.parent/'erdos-bridge-spike'
BIN=Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0/bin'
CACHE=ROOT/'lean-controls/.lake/packages'
DEPS=sorted(p/'.lake/build/lib/lean' for p in CACHE.iterdir() if (p/'.lake/build/lib/lean').is_dir())
NEW=['CompletionBranch','GreedyExtension','AveragingBridge','WeightedProfile','ProfileBound','FiniteAveraging','CaseTwo','CompletionEnvelope','PiecewiseCompletion','CutWitness','ScalarCertificate','CutScalar','FixedCutBound']
SOURCES={'Erdos128.GraphBasics':BRIDGE/'Erdos128/GraphBasics.lean','DeletionBridge':BRIDGE/'DeletionBridge.lean'}
SOURCES.update({m:HERE/(m+'.lean') for m in NEW})
for m in ['ExternalInputs','GraphRational','BalancedBlowup','Rounding','RoundingIterate','RoundingFinal']:
    SOURCES['Erdos128.'+m]=HERE/'Erdos128'/(m+'.lean')
SOURCES['PublishedBCL']=HERE/'PublishedBCL.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={m:sha(p) for m,p in SOURCES.items()}
replay=Path(tempfile.mkdtemp(prefix='full-bound-source-',dir=HERE))
for m,p in SOURCES.items():
    target=replay/Path(m.replace('.','/')).with_suffix('.lean')
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,target)
env=os.environ.copy();env['PATH']=str(BIN)+os.pathsep+env.get('PATH','')
env['LEAN_PATH']=os.pathsep.join(map(str,[replay,*DEPS]))
result={'date':'2026-10-17','scope':'All finite orders, integral floor-half bound 2587/100000 conditional only on the stated published eventual BCL cut theorem',
'sources_before':before,'sources_origin':{m:str(p)for m,p in SOURCES.items()},'fresh_directory':str(replay),
'dependency_policy':'Only fresh copied local sources and existing pinned Mathlib package artifacts; no original bridge or controls oleans',
'lean_path':env['LEAN_PATH'],'lean':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),
'mathlib_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=CACHE/'mathlib',text=True).strip(),
'axioms':{},'runs':[]}
allowed={'propext','Classical.choice','Quot.sound'}
def save():
    result['sources_after']={m:sha(p)for m,p in SOURCES.items()}
    result['source_stable']=result['sources_after']==before
    (HERE/'full-bound-verification.json').write_text(json.dumps(result,indent=2)+'\n')
for m in SOURCES:
    rel=Path(m.replace('.','/'))
    command=[str(BIN/'lean'),'-o',str(rel.with_suffix('.olean')),str(rel.with_suffix('.lean'))]
    t=time.monotonic();p=subprocess.run(command,cwd=replay,env=env,text=True,capture_output=True)
    log='full-bound-verified-'+m.replace('.','-')+'.log';(HERE/log).write_text(p.stdout+p.stderr)
    result['runs'].append({'module':m,'command':command,'exit':p.returncode,'seconds':time.monotonic()-t,'log':log})
    result['axioms'].update({name:[a.strip()for a in axs.split(',')]for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",p.stdout)})
    if p.returncode:save();raise SystemExit('Compilation failed: '+m)
    if any(set(axs)-allowed for axs in result['axioms'].values()):save();raise SystemExit('Unexpected axiom')
command=[str(BIN/'leanchecker'),*SOURCES,'-v']
t=time.monotonic();p=subprocess.run(command,cwd=replay,env=env,text=True,capture_output=True)
log='full-bound-verified-kernel-replay.log';(HERE/log).write_text(p.stdout+p.stderr)
result['runs'].append({'command':command,'exit':p.returncode,'seconds':time.monotonic()-t,'log':log})
result['kernel_replay_scope']='All twenty-two local modules replayed into their import environments; cached Mathlib dependencies trusted'
result['completion_namespace_audited_declarations']=sum(name.startswith('Erdos128.CompletionBridge.')for name in result['axioms'])
result['local_module_count']=len(SOURCES)
result['reused_transport_declarations']=2
result['conditional_input']='Explicit theorem parameter hBCL: exists N, all finite triangle-free graphs of order at least N admit an internal cut cost at most (2/47)*n^2. This premise is NOT discharged by the standard-axiom audit.'
result['attribution']='38 audited completion-namespace declarations include 2 copied BCL transport proofs; 17 scalar declarations and baseline graph, blow-up and rounding proofs are attributed upstream. Count is verification inventory, not novelty.'
result['passed']=p.returncode==0 and result['completion_namespace_audited_declarations']==38 and all(sha(p)==before[m]for m,p in SOURCES.items())
save()
print(json.dumps({'passed':result['passed'],'audited_completion_declarations':result['completion_namespace_audited_declarations'],'seconds':sum(r['seconds']for r in result['runs'])}))
raise SystemExit(0 if result['passed'] else 1)
