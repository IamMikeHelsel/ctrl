"""Preserve this round's source, paper and evidence; omit compiled caches."""
from pathlib import Path
import hashlib,json,shutil,argparse
P=argparse.ArgumentParser();P.add_argument('destination',type=Path);a=P.parse_args()
root=Path(__file__).resolve().parent
skip_dirs={'.git','.lake','.replay','.cache','cache','__pycache__','rendered','attempts'}
skip_suffixes=('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.pyc','.zip')
files={}
for p in sorted(root.rglob('*')):
 if not p.is_file() or p.is_symlink() or p.name=='.DS_Store':continue
 r=p.relative_to(root)
 if any(x in skip_dirs or x.startswith('gu-skew-') for x in r.parts):continue
 if p.name.endswith(skip_suffixes):continue
 # Public source PDF can be retrieved from its recorded URL; no need to redistribute it.
 if p.name=='author-draft-live.pdf':continue
 data=p.read_bytes();out=a.destination/r
 out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists() and out.read_bytes()!=data:
  raise SystemExit(f'Refusing to overwrite changed snapshot file: {r}')
 out.write_bytes(data)
 files[str(r)]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
manifest={'scope':'Source, manuscript and verification evidence; compiled caches excluded.',
 'source':str(root),'files':files}
(a.destination/'PRESERVATION.json').write_text(json.dumps(manifest,indent=2)+'\n')
for rel,info in files.items():
 assert hashlib.sha256((a.destination/rel).read_bytes()).hexdigest()==info['sha256']
print(json.dumps({'files':len(files),'bytes':sum(v['bytes'] for v in files.values()),'all_hashes_match':True,'destination':str(a.destination)}))
