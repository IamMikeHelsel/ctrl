from pathlib import Path
import hashlib,json,datetime
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
MANIFESTS=[
 'research/overnight/2026-10-18/robot-motion/critic-04/artifact-sha256.json',
 'research/overnight/2026-10-18/controls/critic-04/artifact-sha256.json',
 'research/overnight/2026-10-18/geometric-unity/critic-04/SHA256SUMS',
 'research/overnight/2026-10-18/publication-review-01/artifact-sha256.json',
 'research/overnight/2026-10-18/robot-motion/smooth-review-01/artifact-sha256.json',
]
READ=[
 'AGENTS.md','research/overnight/2026-10-18/README.txt',
 'research/overnight/2026-10-18/state.json',
 'research/overnight/2026-10-18/robot-motion/builder-04/VelocityAdmission.lean',
 'research/overnight/2026-10-18/robot-motion/builder-04/CLAIMS.txt',
 'research/overnight/2026-10-18/controls/builder-04/QuadraticTrajectory.lean',
 'research/overnight/2026-10-18/geometric-unity/critic-01/QUESTIONS-FOR-AUTHOR.txt',
 'research/overnight/2026-10-18/geometric-unity/critic-04/NEXT-GATE.txt',
 'research/overnight/2026-10-18/publication-review-01/source-review.txt',
 'publication/robot-motion/checked-motion-paper/main.tex',
 'publication/robot-motion/execution-note/related-work-audit/comparison.md',
 'research/overnight/2026-10-18/fir-source-review-01/biagiotti2012.pdf',
 'research/overnight/2026-10-18/fir-source-review-01/biagiotti2012.txt',
 'research/overnight/2026-10-18/robot-motion/smooth-baseline-01/ERRATA-01.txt',
]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
out={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope':'Progress and scope review; no proof compilation, solver or physical replay repeated.', 'manifest_checks':[], 'read_file_hashes':{}}
for rel in MANIFESTS:
 p=ROOT/rel
 if p.suffix=='.json':
  rows=json.loads(p.read_text())['files'].items()
 else:
  rows=[(line.split('  ',1)[1],line.split('  ',1)[0]) for line in p.read_text().splitlines() if line.strip()]
 checked=[];bad=[]
 for name,entry in rows:
  expected=entry if isinstance(entry,str) else entry['sha256']
  f=p.parent/name
  actual=sha(f) if f.is_file() else None
  checked.append(name)
  if actual!=expected: bad.append({'path':name,'expected':expected,'actual':actual})
 out['manifest_checks'].append({'path':rel,'sha256':sha(p),'checked_files':len(checked),'mismatches':bad})
for rel in READ:
 out['read_file_hashes'][rel]=sha(ROOT/rel)
out['all_frozen_inputs_match']=all(not d['mismatches'] for d in out['manifest_checks'])
(HERE/'input-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='read_file_hashes'},indent=2))
assert out['all_frozen_inputs_match']
