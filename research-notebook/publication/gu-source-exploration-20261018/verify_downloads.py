"""Verify stored external source bytes; never executes downloaded code."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
checks=[]
def verify(p,row):
    data=p.read_bytes()
    if len(data)!=row['bytes'] or hashlib.sha256(data).hexdigest()!=row['sha256']:
        raise RuntimeError(f'Hash mismatch: {p}')
    checks.append(str(p.relative_to(root)))
for row in json.loads((root/'sources/provenance.json').read_text()):
    if row['status']=='downloaded': verify(root/'sources'/row['path'],row)
for row in json.loads((root/'sources/derived-manifest.json').read_text()):
    verify(root/'sources'/row['path'],row)
for row in json.loads((root/'software/DOWNLOAD-MANIFEST.json').read_text())['files']:
    p=root/'software/sources'/row['repo'].replace('/','--')/row['path']
    verify(p,row)
    data=p.read_bytes()
    git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    if git!=row['git_blob_sha1']: raise RuntimeError(f'Git blob mismatch: {p}')
result={'status':'PASS','checked_files':len(checks),'scope':'Downloaded primary sources, extracted derivatives and selected repository files match recorded hashes; does not validate their mathematical claims'}
(root/'DOWNLOAD-VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
