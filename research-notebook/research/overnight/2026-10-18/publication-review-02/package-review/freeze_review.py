from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path(__file__).resolve().parent
assert json.loads((R/'result.json').read_text())['artifact_gate']=='PASS'
assert not (R/'artifact-sha256.json').exists(),'Review already frozen'
assert not any(p.is_symlink() for p in R.rglob('*')),'Unexpected symlink'
files={}
for p in sorted(R.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(R)
 if any(x in {'__pycache__','.build','.cache'} for x in rel.parts):continue
 if '.olean' in p.name or p.suffix in {'.ilean','.pyc'}:continue
 data=p.read_bytes();files[str(rel)]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
manifest={'purpose':'Independent final V4 portable package review; preserves V2 pin counterexample, V3 output-snapshot counterexample, fresh source replays and final client proof/failure evidence. Compiled caches excluded; their hashes remain in replay/client records.','created_utc':datetime.now(timezone.utc).isoformat(),'files':files}
p=R/'artifact-sha256.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
for name,v in files.items():assert hashlib.sha256((R/name).read_bytes()).hexdigest()==v['sha256']
print(json.dumps({'manifest':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'files':len(files),'bytes':sum(x['bytes'] for x in files.values())},indent=2))
