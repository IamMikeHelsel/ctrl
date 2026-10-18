"""Check scratch proofs against cached frozen imports; no project source writes."""
import concurrent.futures, hashlib, json, os, re, subprocess, time
from pathlib import Path
OUT=Path(__file__).resolve().parent
BASE=OUT.parents[2]; PROJECT=BASE/'lean-controls'
env=os.environ.copy();env['ELAN_HOME']=str(BASE/'.tools/elan')
exe=str(BASE/'.tools/elan/bin/lake')
def check(p):
 t=time.perf_counter()
 run=subprocess.run([exe,'env','lean',str(p)],cwd=PROJECT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=p.with_suffix('.verification.log');log.write_text(run.stdout)
 ax=re.findall(r"depends on axioms: \[([^\]]*)\]",run.stdout,re.S)
 allowed={'propext','Classical.choice','Quot.sound'}
 unexpected=sorted({a.strip() for x in ax for a in x.replace('\n','').split(',') if a.strip()}-allowed)
 return {'file':str(p.relative_to(OUT)),'exit_code':run.returncode,'seconds':round(time.perf_counter()-t,3),
  'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(), 'audit_count':len(ax),'unexpected_axioms':unexpected,'log':str(log.relative_to(OUT))}
files=sorted((OUT/'tight-sector').glob('*.lean'))
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex: results=list(ex.map(check,files))
result={'kind':'scratch generated-vertex checking with original pinned cached imports; not full uncertainty safety proof',
 'results':results,'all_pass':all(x['exit_code']==0 and x['audit_count']==1 and not x['unexpected_axioms'] for x in results)}
(OUT/'vertex-replay.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
