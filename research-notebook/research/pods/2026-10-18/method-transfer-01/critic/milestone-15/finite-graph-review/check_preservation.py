#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,difflib,re
P=Path(__file__).resolve().parent
ROOT=next(x for x in P.parents if (x/'lean-controls').is_dir())
COPY=P/'builder-copy'; ORIGINAL=ROOT/'research/pods/2026-10-18/method-transfer-01/erdos/finite-graph-09'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=json.loads((COPY/'INPUTS.json').read_text())
manifest=json.loads((COPY/'artifact-sha256.json').read_text())
assert sha(ORIGINAL/'artifact-sha256.json')==sha(COPY/'artifact-sha256.json')=='ac731e5eac922097a38b58eacdf6a062c6f4d495f9a24903376351f391d2eb79'
for rel,h in manifest['files'].items(): assert sha(ORIGINAL/rel)==sha(COPY/rel)==h,rel
prior=[]
for item in inputs['prior_freezes']:
 mf=ROOT/item['manifest'];assert sha(mf)==item['sha256']
 data=json.loads(mf.read_text())
 for rel,h in data['files'].items():assert sha(mf.parent/rel)==h,(mf,rel)
 prior.append({'manifest':item['manifest'],'sha256':sha(mf),'files':len(data['files'])})
for name in ['lean-controls/lean-toolchain','lean-controls/lake-manifest.json']:
 assert sha(ROOT/name)==inputs['files'][name]
up=[]
for v in inputs['upstream_modules']:
 assert sha(COPY/v['copy'])==sha(ROOT/v['upstream_source'])==v['sha256']
 up.append({'module':v['module'],'sha256':v['sha256']})
assert sha(COPY/'WeightedProfiles.lean')=='31e89a547ef3fa040a08de08956fc79a1ba25a4b101bc9c88414ccb349b8decd'
e=json.loads((COPY/'extraction.json').read_text());source=(COPY/e['source']).read_text();dst=(COPY/'CutHelpers.lean').read_text()
patch=''.join(difflib.unified_diff(source.splitlines(keepends=True),dst.splitlines(keepends=True),fromfile=e['source'],tofile='CutHelpers.lean'))
assert patch==(COPY/'CutHelpers.patch').read_text()
norm=lambda x:' '.join(x.split())
ranges=[]
for lo,hi in e['line_ranges_inclusive']:
 part=''.join(source.splitlines(keepends=True)[lo-1:hi])
 for name in e['private_made_public']:part=re.sub(r'private (theorem|lemma) '+name+r'\b',r'\1 '+name,part)
 part=part.replace('simpa [largeGraph, edgeCountOn] using hmap','convert hmap using 1 <;> simp [largeGraph, edgeCountOn]\n  congr 1')
 assert norm(part) in norm(dst),(lo,hi)
 ranges.append({'source_lines':[lo,hi],'matches_after_declared_edits_and_whitespace_normalization':True})
# Verify the full diff as well: selected-range substring checks alone would not exclude extra text.
allowed_imports=['Erdos128.LowDensityGraph','Erdos128.WeightedGraph']
assert re.findall(r'^import (.+)$',dst,re.M)==allowed_imports
attempts=json.loads((COPY/'development-attempts.json').read_text())
result={'passed':True,'original_and_review_copy_frozen_entries':len(manifest['files']),'prior_freezes':prior,'prior_file_count':sum(x['files'] for x in prior),'upstream_files_unchanged':up,'accepted_E8_source_unchanged':True,'executed_pins_unchanged':True,'full_patch_exact':True,'extraction_ranges':ranges,'helper_imports':allowed_imports,'builder_failed_attempts_preserved':attempts['failed_attempts'],'scope':'Preservation, extraction and pin checks; no claim of rebuilding upstream original LowDensityConstruction or original Lean4.30'}
(P/'preservation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'E9_files':len(manifest['files']),'prior_files':result['prior_file_count'],'extraction_ranges':len(ranges)},indent=2))
