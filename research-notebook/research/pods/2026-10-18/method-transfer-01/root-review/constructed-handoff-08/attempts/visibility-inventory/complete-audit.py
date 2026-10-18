from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,subprocess,time
R=Path(__file__).resolve().parent; B=R.parents[1]/'controls/constructed-handoff-08'; F=R/'fresh-replay'; L=R/'verification-logs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 v=json.loads((R/'verification.json').read_text());assert v['passed'],'Main independent replay must pass first.'
 inv=json.loads((R/'independent-audit-inventory.json').read_text());names=inv['full_names'];assert len(names)==len(set(names))==317
 frozen=(B/'frozen-manifest.json').read_bytes();assert sha(B/'frozen-manifest.json')==v['builder_manifest_sha256']
 def preserve():
  assert (B/'frozen-manifest.json').read_bytes()==frozen
  assert all(sha(B/n)==h for n,h in json.loads(frozen)['files'].items())
 preserve()
 lean=Path(v['steps'][0]['command'][0]);checker=lean.with_name('leanchecker')
 assert sha(lean)==v['lean_sha256'] and sha(checker)==v['leanchecker_sha256']
 env=os.environ.copy();env['LEAN_PATH']=v['lean_path'];env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
 f=F/'CompleteAudit.lean';assert not f.exists();f.write_text('import HandoffWitness\n'+''.join('#print axioms '+n+'\n' for n in names))
 report={'passed':False,'unique_closures':317,'additional_names':inv['extra_lemma_audits'],'source_sha256':sha(f),'steps':[],'axioms':{}}
 for label,argv in [('complete-axiom-audit',[lean,'--root='+str(F),'-o',f.with_suffix('.olean'),f]),('kernel-CompleteAudit',[checker,'CompleteAudit','-v'])]:
  remaining=(datetime(2026,10,18,21,35,tzinfo=timezone.utc)-datetime.now(timezone.utc)).total_seconds();assert remaining>1
  start=time.monotonic();log=L/(label+'.log')
  with log.open('w') as out:proc=subprocess.run(list(map(str,argv)),cwd=F,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=min(180,remaining))
  report['steps'].append({'label':label,'command':list(map(str,argv)),'exit_code':proc.returncode,'passed':proc.returncode==0,'seconds':round(time.monotonic()-start,4),'log_sha256':sha(log)})
  (R/'complete-audit-result.json').write_text(json.dumps(report,indent=2)+'\n');assert proc.returncode==0
  if label=='complete-axiom-audit':
   raw=log.read_text()
   for n,body in re.findall(r"^'(.+)' depends on axioms: \[([^]]*)\]",raw,re.M):
    axioms={s.strip() for s in body.split(',') if s.strip()};assert axioms<={'propext','Classical.choice','Quot.sound'}
    assert n not in report['axioms'];report['axioms'][n]=sorted(axioms)
   for n in re.findall(r"^'(.+)' does not depend on any axioms",raw,re.M):
    assert n not in report['axioms'];report['axioms'][n]=[]
   assert set(report['axioms'])==set(names)
 preserve();report['passed']=True;report['builder_preserved']=True
 (R/'complete-audit-result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'passed':True,'unique_closures':317,'extra_steps':2}))
if __name__=='__main__':main()
