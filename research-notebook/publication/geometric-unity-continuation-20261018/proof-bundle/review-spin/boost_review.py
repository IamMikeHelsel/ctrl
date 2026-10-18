from pathlib import Path
import json,os,subprocess,time,shutil,hashlib
B=Path(__file__).resolve().parent; P=B.parent;latest=P/json.loads((P/'latest-result.json').read_text())['run']/'environment.json';E=json.loads(latest.read_text());env=os.environ.copy();env['LEAN_PATH']=str(B)+':'+str(P/'review-algebra')+':'+E['LEAN_PATH'];env['PATH']=str(Path(E['compiler']).parent)+':'+env['PATH'];steps=[]
def run(n,args,negative=False):
 t=time.monotonic();r=subprocess.run(args,cwd=B,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600);(B/(n+'.log')).write_text(r.stdout);steps.append({'name':n,'code':r.returncode,'seconds':time.monotonic()-t});print(n,r.returncode,flush=True)
 if negative:assert r.returncode!=0 and 'unsolved goals' in r.stdout and not any(w in r.stdout for w in ['unknown identifier','type mismatch','unexpected token']),r.stdout
 else:assert r.returncode==0,r.stdout
 return r.stdout
for m in ['RationalBoost','BoostClient']:
 run('build-'+m,[E['compiler'],'-o',str(B/(m+'.olean')),str(B/(m+'.lean'))])
 run('kernel-'+m,[str(Path(E['compiler']).with_name('leanchecker')),m,'-v'])
for p in B.glob('FalseBoost*.lean.txt'):
 q=B/p.name.removesuffix('.txt');shutil.copyfile(p,q);run(q.stem,[E['compiler'],str(q)],True)
audit=(P/'controls/FinalAudit.lean').read_text().replace('import CounterWitnesses','import BoostClient').replace('`CounterWitnesses]', '`CounterWitnesses, `RationalBoost, `BoostClient]');(B/'BoostAudit.lean').write_text(audit);out=run('BoostAudit',[E['compiler'],str(B/'BoostAudit.lean')]);rows=[x for x in out.splitlines() if x.startswith('AUDIT|RationalBoost|') or x.startswith('AUDIT|BoostClient|')];assert len(rows)>=10
(B/'boost-result.json').write_text(json.dumps({'status':'PASS','steps':steps,'audited_new_declarations':rows,'source_sha256':hashlib.sha256((B/'RationalBoost.lean').read_bytes()).hexdigest()},indent=2)+'\n')
