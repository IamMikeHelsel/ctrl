"""Audit all frozen modules explicitly, including the separately imported order controls."""
from pathlib import Path
import json,os,subprocess,time,hashlib
D=Path(__file__).resolve().parent;R=D.parents[4];B=D.parent/'builder-04';T=D/'cache/fresh-02'
mods=sorted(p.stem for p in B.glob('*.lean'))+['ReviewClient']
base=(D/'Audit.lean.txt').read_text();s='\n'.join('import '+m for m in mods)+'\n'+base[base.index('open Lean Elab Command'):]
(D/'FullAudit.lean.txt').write_text(s);(T/'FullAudit.lean').write_text(s)
e=json.loads((D/'environment.json').read_text());env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan');env['LEAN_PATH']=e['paths']
lean=subprocess.check_output([str(R/'.tools/elan/bin/lake'),'env','which','lean'],cwd=R/'lean-controls',env=env,text=True).strip();env['PATH']=str(Path(lean).parent)+':'+env['PATH']
start=time.monotonic();p=subprocess.run([lean,str(T/'FullAudit.lean')],cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
(D/'logs/FullAudit.txt').write_text(p.stdout);assert p.returncode==0,p.stdout
rows=[s for s in p.stdout.splitlines() if s.startswith('DECL|')]
counts={m:sum(s.split('|')[1]==m for s in rows) for m in mods};assert all(counts.values()),counts
out={'status':'PASS','all_local_declarations_audited':len(rows),'module_counts':counts,'audit_source_sha256':hashlib.sha256((D/'FullAudit.lean.txt').read_bytes()).hexdigest(),'command':[lean,str(T/'FullAudit.lean')],'seconds':time.monotonic()-start,'reason':'The order-control source is a separate module, not an import of ComplexControls. Explicit full-closure imports avoid omitting it from the environment audit.'}
(D/'full-audit-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
