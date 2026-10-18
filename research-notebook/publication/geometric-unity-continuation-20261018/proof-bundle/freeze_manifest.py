#!/usr/bin/env python3
"""Hash portable artifacts. Build products and this manifest itself are excluded."""
from pathlib import Path
import hashlib
B=Path(__file__).resolve().parent
skipdirs={'.lake','.replay','__pycache__','release'}
files=[]
for p in B.rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(B)
 if any(part in skipdirs for part in rel.parts):continue
 if p.name=='SHA256SUMS' or '.olean' in p.name or p.suffix in {'.ilean','.pyc'}:continue
 files.append(p)
(B/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(B))+'\n' for p in sorted(files)))
print('Hashed',len(files),'portable files')
