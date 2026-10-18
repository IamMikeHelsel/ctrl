#!/usr/bin/env python3
"""Fresh local dependency closure, public axiom audit, replay and false controls."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
import dev
import generate_reference

HERE=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
TARGETS=['FrozenReference','DirectReference']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def statements(p):
    text=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',text),p
    namespaces=re.findall(r'^namespace (\S+)',text,re.M)
    assert len(namespaces)==1,(p,namespaces)
    names=[]
    for line in text.splitlines():
        m=re.match(r'^\s*(.*?)\b(?:theorem|lemma)\s+([^\s{(:]+)',line)
        if m and not re.search(r'\bprivate\b',m.group(1)):
            names.append(namespaces[0]+'.'+m.group(2))
    return names

def main():
    env,lean,dep=dev.environment()
    checker=str(Path(lean).with_name('leanchecker'))
    sources=dev.source_closure()
    assert len(sources)==38
    assert (HERE/'FrozenReference.lean').read_text()==generate_reference.render()
    binding=json.loads((HERE/'reference-binding.json').read_text())
    assert binding['input_sha256']==sha(generate_reference.SOURCE)
    assert binding['output_sha256']==sha(HERE/'FrozenReference.lean')
    assert binding['generator_sha256']==sha(HERE/'generate_reference.py')
    public={m:statements(p) for m,p in sources.items()}
    names=[name for ns in public.values() for name in ns]
    assert names and len(names)==len(set(names))
    logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
    mathlib=dev.BASE/'.lake/packages/mathlib'
    report={'passed':False,
      'scope':'All38 local modules in the target dependency closure copied and compiled fresh. Cached pinned Mathlib dependencies reused. All public local theorems audited. Separate leanchecker replay for both new target modules and the scaled tracking bridge.',
      'toolchain':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
      'lean_toolchain_file':(dev.BASE/'lean-toolchain').read_text().strip(),
      'mathlib_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip(),
      'mathlib_status':subprocess.check_output(['git','status','--porcelain'],cwd=mathlib,text=True),
      'lake_manifest_sha256':sha(dev.BASE/'lake-manifest.json'),
      'source_paths':{m:str(p.relative_to(dev.WORK)) for m,p in sources.items()},
      'source_sha256':{m:sha(p) for m,p in sources.items()},
      'verifier_sha256':sha(Path(__file__)), 'build_helper_sha256':sha(HERE/'dev.py'),
      'reference_binding':binding,'reference_generation_reproduced':True,
      'public_statements_by_module':public,'steps':[],'axioms':{}}
    def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(label,args,cwd,renv,negative=False):
        start=time.monotonic();log=logs/(label+'.log')
        with log.open('w') as out:
            proc=subprocess.run(args,cwd=cwd,env=renv,stdout=out,stderr=subprocess.STDOUT,timeout=600)
        ok=proc.returncode!=0 if negative else proc.returncode==0
        report['steps'].append({'label':label,'exit_code':proc.returncode,'passed':ok,
          'expected':'rejection' if negative else 'success','seconds':time.monotonic()-start,'log_sha256':sha(log)})
        save();print(label,proc.returncode,flush=True);assert ok,label
    with tempfile.TemporaryDirectory(prefix='fresh-',dir=HERE/'build') as tmp:
        root=Path(tmp);renv=env.copy();renv['LEAN_PATH']=str(root)+':'+dep
        renv['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
        for m,p in sources.items():
            dst=root/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(p,dst)
            run('build-'+m,[lean,'--root='+str(root),'-o',str(dst.with_suffix('.olean')),str(dst)],root,renv)
        (root/'Audit.lean').write_text('import DirectReference\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
        run('axiom-audit',[lean,str(root/'Audit.lean')],root,renv)
        for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(logs/'axiom-audit.log').read_text()):
            axioms={x.strip() for x in raw.split(',') if x.strip()}
            assert axioms<=ALLOWED,(name,axioms)
            report['axioms'][name]=sorted(axioms)
        assert set(report['axioms'])==set(names),set(names)-set(report['axioms'])
        for m in ['ScaledTracking']+TARGETS:
            run('kernel-'+m,[checker,m,'-v'],root,renv)
        original=(root/'DirectReference.lean').read_text()
        old='    |jerk k t| ≤ 10 := by\n  interval_cases k'
        assert original.count(old)==1
        false=original.replace(old,'    |jerk k t| ≤ 9 := by\n  interval_cases k')
        (root/'FalseJerkBound.lean').write_text(false)
        run('reject-false-jerk-bound',[lean,str(root/'FalseJerkBound.lean')],root,renv,negative=True)
        bad=(logs/'reject-false-jerk-bound.log').read_text()
        assert ('unsolved goals' in bad or 'linarith failed' in bad) and 'error: unknown' not in bad
        # A one-unit rational coefficient error destroys the matched reference.
        mut=root/'changed-join';mut.mkdir()
        frozen=(root/'FrozenReference.lean').read_text()
        old='C (44217/1600000)'
        assert frozen.count(old)==1
        (mut/'FrozenReference.lean').write_text(frozen.replace(old,'C (44218/1600000)'))
        shutil.copy2(root/'DirectReference.lean',mut/'DirectReference.lean')
        menv=renv.copy();menv['LEAN_PATH']=str(mut)+':'+renv['LEAN_PATH']
        run('build-mutated-reference',[lean,'--root='+str(mut),'-o',str(mut/'FrozenReference.olean'),str(mut/'FrozenReference.lean')],mut,menv)
        run('reject-mismatched-reference-join',[lean,'--root='+str(mut),str(mut/'DirectReference.lean')],mut,menv,negative=True)
        bad=(logs/'reject-mismatched-reference-join.log').read_text()
        assert 'unsolved goals' in bad and 'error: unknown' not in bad
        witness='''import DirectReference
open LeanControls.DirectReference
example : ¬ |jerk 0 0| ≤ (9 : ℝ) := by rw [initial_jerk]; norm_num
example : (44218/1600000 : ℝ) ≠ 44217/1600000 := by norm_num
'''
        (HERE/'MutationWitness.lean').write_text(witness)
        (root/'MutationWitness.lean').write_text(witness)
        run('accepted-mutation-witnesses',[lean,str(root/'MutationWitness.lean')],root,renv)
        report['negative_controls']={
          'jerk_bound':'False limit9 rejected; the accepted initial_jerk theorem gives exactly10.',
          'join':'Perturbing only the reversal phase initial position by1/1600000 leaves a reference jump and fails the reference_matches proof. The perturbed data module itself compiles.'}
    report['source_unchanged']=all(sha(p)==report['source_sha256'][m] for m,p in sources.items())
    report['frozen_reference_unchanged']=sha(generate_reference.SOURCE)==binding['input_sha256']
    report['passed']=report['source_unchanged'] and report['frozen_reference_unchanged'] and all(s['passed'] for s in report['steps'])
    save();print(json.dumps({'passed':report['passed'],'public_local_theorems':len(names),'fresh_local_modules':len(sources)}))
if __name__=='__main__':main()
