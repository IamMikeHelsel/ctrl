#!/usr/bin/env python3
"""Fresh source closure, public-axiom audit, kernel replay and false controls."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
import dev
HERE=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
TARGETS=['ConstantBias','BiasFixtures','DirectBias','BiasWitness']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def statements(p):
    code=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code),p
    ns=re.findall(r'^namespace (\S+)',code,re.M); assert len(ns)==1,(p,ns)
    names=[]
    for line in code.splitlines():
        m=re.match(r'^\s*(.*?)\b(?:theorem|lemma)\s+([^\s{(:]+)',line)
        if m and not re.search(r'\bprivate\b',m.group(1)):names.append(ns[0]+'.'+m.group(2))
    return names

def main():
    env,lean,dep=dev.environment();checker=str(Path(lean).with_name('leanchecker'))
    sources=dev.source_closure()
    public={m:statements(p) for m,p in sources.items()};names=[n for group in public.values() for n in group]
    assert len(names)==len(set(names))
    logs=HERE/'verification-logs';logs.mkdir(exist_ok=True);(HERE/'build').mkdir(exist_ok=True)
    mathlib=dev.BASE/'.lake/packages/mathlib'
    report={'passed':False,'scope':'Every local source in closure compiled fresh; cached pinned Mathlib reused. Every public local theorem audited. Target modules and inherited plant bridge receive separate leanchecker replay.',
      'toolchain':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
      'lean_toolchain_file':(dev.BASE/'lean-toolchain').read_text().strip(),
      'mathlib_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip(),
      'mathlib_status':subprocess.check_output(['git','status','--porcelain'],cwd=mathlib,text=True),
      'lake_manifest_sha256':sha(dev.BASE/'lake-manifest.json'),
      'source_paths':{m:str(p.relative_to(dev.WORK)) for m,p in sources.items()},
      'source_sha256':{m:sha(p) for m,p in sources.items()},
      'verifier_sha256':sha(Path(__file__)),'helper_sha256':sha(HERE/'dev.py'),
      'public_statements_by_module':public,'steps':[],'axioms':{}}
    def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(label,args,cwd,renv,negative=False):
        log=logs/(label+'.log');start=time.monotonic()
        with log.open('w') as out:proc=subprocess.run(args,cwd=cwd,env=renv,stdout=out,stderr=subprocess.STDOUT,timeout=600)
        ok=proc.returncode!=0 if negative else proc.returncode==0
        report['steps'].append({'label':label,'exit_code':proc.returncode,'passed':ok,'expected':'rejection' if negative else 'success','seconds':time.monotonic()-start,'log_sha256':sha(log)})
        save();print(label,proc.returncode,flush=True);assert ok,label
    with tempfile.TemporaryDirectory(prefix='fresh-',dir=HERE/'build') as tmp:
        root=Path(tmp);renv=env.copy();renv['LEAN_PATH']=str(root)+':'+dep
        renv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
        for m,p in sources.items():
            dst=root/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
            run('build-'+m,[lean,'--root='+str(root),'-o',str(dst.with_suffix('.olean')),str(dst)],root,renv)
        (root/'Audit.lean').write_text('import DirectBias\nimport BiasWitness\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
        run('axiom-audit',[lean,str(root/'Audit.lean')],root,renv)
        for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
            axs={x.strip() for x in raw.split(',') if x.strip()};assert axs<=ALLOWED,(name,axs);report['axioms'][name]=sorted(axs)
        assert set(report['axioms'])==set(names),set(names)-set(report['axioms'])
        for m in ['Settling','ScaledTracking','DirectReference']+TARGETS:
            run('kernel-'+m,[checker,m,'-v'],root,renv)
        controls = {
          'wrong-sign': """import BiasWitness
open LeanControls.UncertainLag LeanControls.Settling LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.ConstantBias
example : holdInput 10 0 (fun _ => (![0,0,0] : State)) 0+(1/100:ℝ) =
  holdInput 10 (0-offset 10 (1/100)) (fun _ => (![0,0,0] : State)) 0 := by
  norm_num [holdInput,command,scaleState,offset]
""",
          'double-count-bias': """import BiasWitness
open LeanControls.Settling LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.ConstantBias LeanControls.BiasWitness
example : 80*(holdInput 10 (offset 10 (1/100)) biasedRest 0+(1/100:ℝ)-biasedRest 0 2) = 0 := by
  norm_num [holdInput,command,scaleState,offset,biasedRest]
""",
          'drop-position-offset': """import BiasWitness
open LeanControls.BiasWitness
example : |biasedRest 2 0-(0:ℝ)| ≤ 17/16384000 := by
  norm_num [biasedRest]
"""}
        for label,code in controls.items():
            p=root/(label.replace('-','_')+'.lean');p.write_text(code)
            run('reject-'+label,[lean,str(p)],root,renv,negative=True)
            bad=(logs/('reject-'+label+'.log')).read_text()
            assert 'unsolved goals' in bad and 'error: unknown' not in bad and 'timeout' not in bad,label
    report['source_unchanged']=all(sha(p)==report['source_sha256'][m] for m,p in sources.items())
    report['passed']=report['source_unchanged'] and all(s['passed'] for s in report['steps'])
    report['public_local_statement_count']=len(names);report['fresh_local_module_count']=len(sources)
    report['negative_controls']={'wrong_sign':'The actual controller-plus-bias field requires the positive analysis offset.','double_count':'Changing the actual goal to the analysis equilibrium produces derivative 4/5 rather than zero at the true equilibrium.','missing_offset':'A real constant-bias resting trajectory violates the proposed position transient bound when its goal offset is omitted.'}
    save();print(json.dumps({'passed':report['passed'],'public_local_statements':len(names),'fresh_modules':len(sources)}))
if __name__=='__main__':main()
