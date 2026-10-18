"""Preserve original analyses/reconstruction plus retrieval manifests, not third-party corpus."""
from pathlib import Path
import hashlib,json,shutil
root=Path(__file__).resolve().parent
out=Path('/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/publication/gu-source-exploration-20261018')
selected=[]
for p in sorted(root.rglob('*')):
    if not p.is_file(): continue
    rel=p.relative_to(root)
    if '__pycache__' in rel.parts: continue
    if rel.parts[:2]==('software','sources') or rel.parts[:2]==('software','metadata'): continue
    if rel.parts[0]=='sources' and p.name not in {'SOURCE-INVENTORY.md','OPERATOR-REVIEW.txt','download.py','provenance.json','derived-manifest.json'}: continue
    if p.suffix in {'.pdf','.png','.html'} or p.name=='appendix-OCR-NOT-EXECUTABLE.txt': continue
    selected.append(p)
files={}
for p in selected:
    rel=p.relative_to(root); data=p.read_bytes(); dst=out/rel
    dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.exists() and dst.read_bytes()!=data: raise RuntimeError(f'Snapshot would overwrite {rel}')
    dst.write_bytes(data)
    files[str(rel)]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
manifest={'scope':'Original analyses, reconstruction code, results and source retrieval manifests. Raw third-party sources stay in local exploration folder. Previous Lean acceptance unchanged.','source':str(root),'files':files}
(out/'PRESERVATION.json').write_text(json.dumps(manifest,indent=2)+'\n')
for rel,row in files.items():
    if hashlib.sha256((out/rel).read_bytes()).hexdigest()!=row['sha256']: raise RuntimeError(rel)
print(json.dumps({'files':len(files),'destination':str(out),'hashes':'PASS'}))
