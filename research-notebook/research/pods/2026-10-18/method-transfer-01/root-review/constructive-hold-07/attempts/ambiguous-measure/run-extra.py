from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parent
report=json.loads((HERE/'verification.json').read_text())
assert all(s['passed'] for s in report['steps'])
assert len([s for s in report['steps'] if s['label'].startswith('build-')])==45
assert any(s['label']=='axiom-audit' and s['passed'] for s in report['steps'])
# Main kernel replay may still run. Final acceptance also requires its completion.
fresh=HERE/'fresh-replay';src=HERE/'ReviewCausality.lean';dst=fresh/src.name
assert not dst.exists(), 'Preserve prior attempt before rerun'
dst.write_bytes(src.read_bytes())
lean=Path(report['steps'][0]['command'][0]);checker=lean.with_name('leanchecker')
env=os.environ.copy();env['LEAN_PATH']=report['lean_path'];env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
steps=[]
for label,cmd in [('compile',[str(lean),'--root='+str(fresh),'-o',str(dst.with_suffix('.olean')),str(dst)]),('kernel',[str(checker),'ReviewCausality','-v'])]:
 start=time.monotonic()
 p=subprocess.run(cmd,cwd=fresh,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 log=HERE/('extra-'+label+'.log');log.write_text(p.stdout)
 steps.append(dict(label=label,command=cmd,exit_code=p.returncode,seconds=time.monotonic()-start,log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
 (HERE/'extra-result.json').write_text(json.dumps(dict(passed=False,steps=steps),indent=2)+'\n')
 print(label,p.returncode,flush=True)
 assert p.returncode==0,p.stdout
raw=(HERE/'extra-compile.log').read_text()
audit=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",raw)
assert len(audit)==1 and audit[0][0]=='ReviewCausality.finite_history'
axioms={a.strip() for a in audit[0][1].split(',') if a.strip()}
assert axioms<={'propext','Classical.choice','Quot.sound'}
(HERE/'extra-result.json').write_text(json.dumps(dict(passed=True,steps=steps,axioms=sorted(axioms),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest()),indent=2)+'\n')
