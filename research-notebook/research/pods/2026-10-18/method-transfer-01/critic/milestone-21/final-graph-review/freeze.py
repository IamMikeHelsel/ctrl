#!/usr/bin/env python3
"""Freeze review source, statements and recorded evidence, excluding build caches."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
H=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((H/'final-check.json').read_text())['passed']
assert json.loads((H/'input-check.json').read_text())['passed']
files={}
for p in sorted(H.rglob('*')):
    if not p.is_file() or p==H/'manifest.json':continue
    if '__pycache__' in p.parts or p.name=='.DS_Store':continue
    if re.search(r'\.(?:olean|ilean|ir)(?:\.|$)',p.name):continue
    files[str(p.relative_to(H))]=sha(p)
out={'frozen_utc':datetime.now(timezone.utc).isoformat(),'scope':'Independent E11 all-finite floor-half .0251 theorem review, conditional on transparent BCLEventual; source/premise review, fresh full local closure, axiom audit, separate kernels, mathematical controls, preserved failures.','excluded':'Compiled Lean products and Python caches. Recorded proof-product hashes remain in verification.json.','files':files}
(H/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
assert all(sha(H/k)==v for k,v in files.items())
print(json.dumps({'files':len(files),'manifest_sha256':sha(H/'manifest.json'),'report_sha256':sha(H/'REPORT.txt'),'final_index_sha256':sha(H/'FINAL-INDEX.json')}))
