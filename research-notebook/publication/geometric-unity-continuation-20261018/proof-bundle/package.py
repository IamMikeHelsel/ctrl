#!/usr/bin/env python3
"""Package the finalized manifest exactly; exclude every unlisted cache product."""
from pathlib import Path
import hashlib,json,zipfile
B=Path(__file__).resolve().parent;O=B.parent/'output';O.mkdir(exist_ok=True)
manifest=B/'SHA256SUMS';entries={}
for line in manifest.read_text().splitlines():
 h,relative=line.split('  ',1);p=B/relative
 if not p.resolve().is_relative_to(B) or hashlib.sha256(p.read_bytes()).hexdigest()!=h:
  raise RuntimeError('Manifest verification failed: '+relative)
 entries[relative]=h
if len(entries)!=len(manifest.read_text().splitlines()):raise RuntimeError('Duplicate manifest entries')
archive=O/'gu-lean-proof-bundle.zip';prefix='gu-lean-proof-bundle/'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for relative in sorted([*entries,'SHA256SUMS']):
  info=zipfile.ZipInfo(prefix+relative,date_time=(2026,10,18,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
  z.writestr(info,(B/relative).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
with zipfile.ZipFile(archive) as z:
 if z.testzip() is not None:raise RuntimeError('Archive CRC failure')
 if set(z.namelist())!={prefix+r for r in [*entries,'SHA256SUMS']}:raise RuntimeError('Archive inventory differs')
 for relative,h in entries.items():
  if hashlib.sha256(z.read(prefix+relative)).hexdigest()!=h:raise RuntimeError('Archived bytes differ: '+relative)
h=hashlib.sha256(archive.read_bytes()).hexdigest();(O/'gu-lean-proof-bundle.zip.sha256').write_text(h+'  '+archive.name+'\n')
result={'status':'PASS','archive':str(archive),'archive_sha256':h,'portable_files':len(entries)+1,'archive_bytes':archive.stat().st_size,'all_manifest_entries_verified_in_archive':True,'caches_included':False}
(O/'gu-lean-proof-bundle-packaging.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
