from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-controls').is_dir())
FROZEN=HERE/'frozen-builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads((FROZEN/'INPUTS.json').read_text())
records=[]
for rec in meta['prior_freezes']:
 p=ROOT/rec['manifest']; assert sha(p)==rec['sha256'],str(p)
 obj=json.loads(p.read_text()); files=obj['files']
 for rel,h in files.items():assert sha(p.parent/rel)==h,(str(p),rel)
 assert len(files)==rec['files_checked']
 dst=HERE/'prior-manifests'/p.parent.name/p.name;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert sha(dst)==sha(p)
 else:shutil.copyfile(p,dst)
 records.append({'manifest':rec['manifest'],'copy':str(dst.relative_to(HERE)),'sha256':sha(p),'checked':len(files)})
upstream=[]
for rec in meta['upstream_modules']:
 assert sha(ROOT/rec['e3_source'])==sha(FROZEN/rec['copy'])==rec['sha256']
 upstream.append({'module':rec['module'],'sha256':rec['sha256'],'matches_e3':True})
for path,h in meta['files'].items():assert sha(ROOT/path)==h,path
packet=ROOT/'research/pods/2026-10-18/method-transfer-01/erdos/weighted-profile-08'
assert sha(packet/'artifact-sha256.json')==sha(FROZEN/'artifact-sha256.json')
bound=json.loads((FROZEN/'artifact-sha256.json').read_text())['files']
for rel,h in bound.items():assert sha(packet/rel)==sha(FROZEN/rel)==h,rel
result={'checked_utc':datetime.now(timezone.utc).isoformat(),'passed':True,'builder_manifest_sha256':sha(packet/'artifact-sha256.json'),'builder_bound_files_verified':len(bound),'prior_packets':records,'prior_files_verified':sum(x['checked'] for x in records),'upstream':upstream,'input_metadata_files_verified':len(meta['files'])}
(HERE/'preservation.json').write_text(json.dumps(result,indent=2)+'\n')
print('preserved',len(bound),'builder files and',result['prior_files_verified'],'prior files')
