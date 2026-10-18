from pathlib import Path
import hashlib, json, os, re, subprocess
root=Path(__file__).resolve().parents[2]; base=root/'lean-controls'; target=Path(__file__).resolve().parent
env=os.environ.copy(); env['ELAN_HOME']=str(root/'.tools/elan')
lake=str(root/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=base,env=env,text=True).strip()
p=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=base,env=env,text=True).strip()
env['LEAN_PATH']=str(target)+':'+':'.join(str((base/x).resolve()) if not Path(x).is_absolute() else x for x in p.split(':'))
env['PATH']=str(Path(lean).parent)+':'+env['PATH']
steps=[]
def run(name,args):
    with (target/(name+'.log')).open('w') as out:
        result=subprocess.run(args,cwd=target,env=env,stdout=out,stderr=subprocess.STDOUT)
    print(name,result.returncode,flush=True)
    steps.append({'name':name,'exit_code':result.returncode})
    if result.returncode:
        print((target/(name+'.log')).read_text()[-8000:]); raise SystemExit(1)
run('compile',[lean,'-o',str(target/'MetricSignature.olean'),str(target/'MetricSignature.lean')])
src=(target/'MetricSignature.lean').read_text()
names=re.findall(r'^theorem (\w+)',src,re.M)
(target/'Audit.lean').write_text('import MetricSignature\n'+'\n'.join('#print axioms WeinsteinLocalCheck.'+n for n in names)+'\n')
run('axioms',[lean,str(target/'Audit.lean')])
run('kernel',[str(Path(lean).with_name('leanchecker')),'MetricSignature','-v'])
axioms={name:[x.strip() for x in deps.split(',') if x.strip()] for name,deps in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(target/'axioms.log').read_text())}
allowed={'propext','Classical.choice','Quot.sound'}
assert len(axioms)==len(names)
assert all(set(v)<=allowed for v in axioms.values())
report={'passed':True,'steps':steps,'axioms':axioms,'theorem_count':len(names),'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'lean':subprocess.check_output([lean,'--version'],text=True).strip(),'mathlib_commit':subprocess.check_output(['git','-C',str(base/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),'scope':'Fresh target source and kernel replay. Pinned mathlib prebuilt dependencies reused.'}
(target/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
