from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs={
 'research/overnight/2026-10-18/robot-motion/builder-02/artifact-sha256.json':'3abb293d650c12e90e1f36dc6296b0b81a2dbbe570692ed4ffdaaaa9f0dacf20',
 'research/overnight/2026-10-18/controls/builder-04/artifact-sha256.json':'fcd32812a407ff8589951ef313da896c106751fef00fa987cfefe4ae64327a9b'}
checks={}
for rel,want in inputs.items():
 p=WORK/rel;assert sha(p)==want
 d=json.loads(p.read_text())['files']
 for f,v in d.items():
  wanted=v if isinstance(v,str) else v['sha256']
  assert sha(p.parent/f)==wanted,(rel,f)
 checks[rel]={'sha256':want,'verified_files':len(d)}
merged={}
for rel in ['research/overnight/2026-10-18/robot-motion/builder-02/source-closure-02.json','research/overnight/2026-10-18/controls/builder-04/source-closure.json']:
 for m,v in json.loads((WORK/rel).read_text()).items():
  assert sha(WORK/v['path'])==v['sha256'],m
  if m in merged: assert merged[m]['sha256']==v['sha256'],m
  else:merged[m]=v
for m,v in merged.items():
 dst=HERE/'inherited'/(m.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert sha(dst)==v['sha256']
 else:shutil.copyfile(WORK/v['path'],dst)
(HERE/'inherited-sources.json').write_text(json.dumps(merged,indent=2)+'\n')
(HERE/'inherited-check.json').write_text(json.dumps(checks,indent=2)+'\n')
print('matched immutable inherited modules',len(merged))
