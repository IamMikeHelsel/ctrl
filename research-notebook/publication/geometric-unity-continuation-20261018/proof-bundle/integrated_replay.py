#!/usr/bin/env python3
"""Fresh compilation, separate kernel replay, false controls, all-declaration audit."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time
if not __debug__ or os.environ.get("PYTHONOPTIMIZE") not in (None, "", "0"):
 raise RuntimeError("Proof replay requires Python assertions enabled; unset PYTHONOPTIMIZE and do not use -O.")
p=argparse.ArgumentParser();p.add_argument('--dependency-project',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--lake',default='lake');a=p.parse_args()
B=Path(__file__).resolve().parent;P=a.dependency_project.resolve(); stamp=time.strftime('%Y%m%d-%H%M%S'); O=B/'logs'/('integrated-'+stamp); C=B/'.replay'/('integrated-'+stamp)
O.mkdir(parents=True);C.mkdir(parents=True);env=os.environ.copy()
(O/'invoked-runner.py').write_bytes(Path(__file__).read_bytes())
(O/'invoked-runner.sha256').write_text(hashlib.sha256(Path(__file__).read_bytes()).hexdigest()+'  invoked-runner.py\n')
subprocess.run([sys.executable,str(B/'inventory_check.py'),'--bundle',str(B),'--output',str(O/'inventory-before.json')],check=True)
def output(cmd,cwd=P):return subprocess.check_output(cmd,cwd=cwd,env=env,text=True).strip()
lean=Path(output([a.lake,'env','which','lean']));version=output([str(lean),'--version']);assert '4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
manifest=json.loads((B/'lake-manifest.json').read_text()); actual=json.loads((P/'lake-manifest.json').read_text())
assert {x['name']:x['rev'] for x in manifest['packages']}=={'mathlib': '56a005855ea17e0b0958f73ec801ae140b0a1679', 'plausible': 'dfa4f38190d07c37e315953e08b90fe2d95b3c24', 'LeanSearchClient': 'd6b4c7be5be75ec4917c873ac50c756dc1436372', 'importGraph': 'a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93', 'proofwidgets': 'df72b022e558978a1c50264cfc4d7fec86fa8e04', 'aesop': '4a174c490d8707121c4a9290800489f105d85e07', 'Qq': 'dce0ad79c486cb1fb504af04f953c3466b0c6db8', 'batteries': '66e469188fe07963e5cf666c7d4433f45b8131c5', 'Cli': 'c24fe6078c630e89b489bffe59b3e20ac30d12c8'}, 'Dependency revisions changed'
assert {x['name']:x['rev'] for x in manifest['packages']}=={x['name']:x['rev'] for x in actual['packages']}
for x in actual['packages']:
 path=P/'.lake/packages'/x['name'];assert output(['git','rev-parse','HEAD'],path)==x['rev']; assert not output(['git','status','--porcelain'],path),path
paths=output([a.lake,'env','printenv','LEAN_PATH']).split(':');deps=[]
for path in paths:
 path=(P/path).resolve()
 if path==(P/'.lake/build/lib/lean').resolve():continue
 assert '/.lake/packages/' in str(path) or path==lean.parent.parent/'lib/lean',path
 deps.append(str(path))
env['LEAN_PATH']=':'.join([str(C)]+deps);env['PATH']=str(lean.parent)+':'+env['PATH']
mods={q.stem:q for q in (B/'source').glob('*.lean')}; pins=json.loads((B/'source-hashes.json').read_text())
for q in mods.values():assert hashlib.sha256(q.read_bytes()).hexdigest()==pins[q.name]
for folder in ['accepted','accepted-controls']:
 for q in (B/folder).glob('*.lean'):
  assert q.stem not in mods,q
  mods[q.stem]=q
for name in ['ReviewerClient','CounterWitnesses']:mods[name]=B/'controls'/(name+'.lean')
accepted_pins=json.loads((B/'accepted-hashes.json').read_text())
for relative,h in accepted_pins.items():assert hashlib.sha256((B/relative).read_bytes()).hexdigest()==h,relative
origin_records=json.loads((B/'accepted-origins.json').read_text())
def verify_originals():
 result={}
 for name,row in origin_records.items():
  original=B.parent/row['origin']
  if original.exists():
   assert hashlib.sha256(original.read_bytes()).hexdigest()==row['sha256'],original
   result[name]='MATCH'
  else:result[name]='original not present; accepted copy pinned'
 return result
original_before=verify_originals()
source_before={m:hashlib.sha256(q.read_bytes()).hexdigest() for m,q in mods.items()}
order=[]
def visit(m):
 if m in order:return
 for n in re.findall(r'^import\s+(\S+)',mods[m].read_text(),re.M):
  if n in mods:visit(n)
 order.append(m)
for m in sorted(mods):visit(m)
(O/'environment.json').write_text(json.dumps({'compiler':str(lean),'version':version,'dependencies':actual,'LEAN_PATH':env['LEAN_PATH'],'fresh_local_source':True},indent=2)+'\n')
steps=[]
def run(label,cmd,negative=False):
 t=time.monotonic();r=subprocess.run(cmd,cwd=C,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600)
 (O/(label+'.txt')).write_text(r.stdout); steps.append({'name':label,'returncode':r.returncode,'seconds':time.monotonic()-t,'command':cmd});(O/'progress.json').write_text(json.dumps(steps,indent=2)+'\n');print(label,r.returncode,flush=True)
 if negative:
  assert r.returncode!=0 and 'unsolved goals' in r.stdout,r.stdout
  assert not any(s in r.stdout.lower() for s in ['unknown identifier','unknown module','type mismatch','unexpected token','failed to synthesize','file not found']),r.stdout
 else:assert r.returncode==0,r.stdout
 return r.stdout
for m in order:
 q=mods[m] if m in mods else B/'controls'/(m+'.lean');raw=q.read_bytes();assert not re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide)\b',raw),q
 (C/(m+'.lean')).write_bytes(raw)
 run('build-'+m,[str(lean),'--root='+str(C),'-o',str(C/(m+'.olean')),str(C/(m+'.lean'))])
for m in order:run('kernel-'+m,[str(lean.with_name('leanchecker')),m,'-v'])
false_sources=list((B/'controls').glob('False*.lean.txt'))+list((B/'accepted-controls').glob('False*.lean.txt'))
for q in sorted(false_sources):
 m=q.name.removesuffix('.lean.txt');shutil.copy2(q,C/(m+'.lean'));run(m,[str(lean),str(C/(m+'.lean'))],True)
audit_source=(B/'controls/FinalAudit.lean').read_text()
audit_source=audit_source.replace('import CounterWitnesses', '\n'.join('import '+m for m in order))
audit_source=re.sub(r'let owned : Array Name := #\[[^\]]*\]', 'let owned : Array Name := #['+', '.join('`'+m for m in order)+']',audit_source)
(C/'FinalAudit.lean').write_text(audit_source);(O/'FinalAudit.lean').write_text(audit_source)
audit=run('FinalAudit',[str(lean),str(C/'FinalAudit.lean')]);rows=[s for s in audit.splitlines() if s.startswith('AUDIT|')]
counts={m:sum(s.startswith('AUDIT|'+m+'|') for s in rows) for m in order};assert all(counts.values())
run('InventoryFinal',[sys.executable,str(B/'inventory_check.py'),'--bundle',str(B),'--run',str(C),'--complete','--output',str(O/'inventory-final.json')])
assert original_before==verify_originals()
assert source_before=={m:hashlib.sha256(q.read_bytes()).hexdigest() for m,q in mods.items()}
result={'original_sources':original_before,'status':'PASS','built_modules':len(order),'kernel_replays':len(order),'false_controls':len(false_sources),'audited_declarations':len(rows),'audit_counts':counts,'source_hashes':{m:hashlib.sha256(q.read_bytes()).hexdigest() for m,q in mods.items()},'steps':steps}
(O/'result.json').write_text(json.dumps(result,indent=2)+'\n');(B/'latest-integrated-result.json').write_text(json.dumps({'run':str(O.relative_to(B)),**result},indent=2)+'\n'); print('PASS',O,flush=True)
