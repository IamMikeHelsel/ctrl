#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,re,difflib
H=Path(__file__).resolve().parent;ROOT=next(p for p in H.parents if (p/'lean-controls').is_dir());BASE=H.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 old=json.loads((H.parent/'formal-cover-10/INPUTS.json').read_text())['prior_freezes']
 old.append({'manifest':'research/pods/2026-10-18/method-transfer-01/erdos/formal-cover-10/artifact-sha256.json','sha256':'7ec490ffe083b7db4767105ef8a4ff5e369e99f46905760f72673a288ac466b4'})
 checks=[]
 for x in old:
  p=ROOT/x['manifest'];assert sha(p)==x['sha256'];d=json.loads(p.read_text())
  for r,s in d['files'].items():assert sha(p.parent/r)==s,(p,r)
  checks.append({'manifest':x['manifest'],'sha256':sha(p),'files_checked':len(d['files']),'all_match':True})
 paths={'AGENTS.md':ROOT/'AGENTS.md','CHARTER.txt':BASE/'CHARTER.txt','final-card.txt':BASE/'root-review/FINAL-GRAPH-INTEGRATION-CARD.txt','statement-gate.txt':BASE/'critic/milestone-18/final-graph-gate/REPORT.txt','statement-gate-manifest.json':BASE/'critic/milestone-18/final-graph-gate/manifest.json','E10-review.txt':BASE/'critic/milestone-20/formal-cover-review/REPORT.txt','E10-semantic-review.txt':BASE/'critic/milestone-20/formal-cover-review/SEMANTIC-REVIEW.txt','E10-review-manifest.json':BASE/'critic/milestone-20/formal-cover-review/manifest.json','executed-lean-toolchain':ROOT/'lean-controls/lean-toolchain','executed-lake-manifest.json':ROOT/'lean-controls/lake-manifest.json','E9-CutHelpers.patch':H.parent/'finite-graph-09/CutHelpers.patch','E9-extraction.json':H.parent/'finite-graph-09/extraction.json','E9-source-notes.txt':H.parent/'finite-graph-09/SOURCE-NOTES.txt','PublishedBCL.lean':BASE/'root-review/final-graph-integration-sources/PublishedBCL.lean','FixedCutBound.lean':BASE/'root-review/final-graph-integration-sources/FixedCutBound.lean'}
 assert sha(paths['statement-gate-manifest.json'])=='4daf7ac8ef536026a1e1d3096902d1a94c6ee8a776a3a9626855dfa0ada3a6ff'
 assert sha(paths['E10-review-manifest.json'])=='b309950601554d490eecd48472a04b53b4afd7026f0be09458a3ab77267a0dc5'
 copies=[]
 for name,p in paths.items():
  dst=H/'inputs'/name;shutil.copyfile(p,dst);copies.append({'original':str(p.relative_to(ROOT)),'copy':str(dst.relative_to(H)),'sha256':sha(p)})
 inherited=json.loads((H/'inherited-closure.json').read_text())['modules'];inherited['FiniteControls']={'path':str((H.parent/'finite-graph-09/FiniteControls.lean').relative_to(ROOT)),'sha256':sha(H.parent/'finite-graph-09/FiniteControls.lean'),'imports':['FiniteGraphBridge']}
 for m,d in inherited.items():assert sha(ROOT/d['path'])==d['sha256']==sha(H/Path(m.replace('.','/')).with_suffix('.lean'))
 upstream_checks=[]
 for p in sorted((H/'Erdos128').glob('*.lean')):
  orig=ROOT/'research/opportunity-assessment/sources/erdos128/lean/Erdos128'/p.name
  assert sha(p)==sha(orig)
  upstream_checks.append({'module':'Erdos128.'+p.stem,'original':str(orig.relative_to(ROOT)),'sha256':sha(p),'byte_identical':True})
 for name in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
  p=H.parent/'finite-graph-09/upstream-original'/name;dst=H/'inputs'/('upstream-'+name);shutil.copyfile(p,dst);copies.append({'original':str(p.relative_to(ROOT)),'copy':str(dst.relative_to(H)),'sha256':sha(p)})
 modules={}
 for p in sorted(H.rglob('*.lean')):
  if p.parent not in [H,H/'Erdos128']:continue
  m=str(p.relative_to(H).with_suffix('')).replace('/','.');modules[m]={'source':str(p.relative_to(H)),'sha256':sha(p),'imports':re.findall(r'^import (.+)$',p.read_text(),re.M)}
 assert 'LowDensityConstruction' not in modules and 'Erdos128.LowDensityConstruction' not in modules
 assert 'PublishedBCL' not in modules and 'FixedCutBound' not in modules
 order=[]
 def visit(m):
  if m in order:return
  for dep in modules[m]['imports']:
   if dep!='Mathlib':assert dep in modules,(m,dep);visit(dep)
  order.append(m)
 visit('FinalControls');assert set(order)==set(modules),(set(modules)-set(order))
 (H/'complete-closure.json').write_text(json.dumps({'order':order,'modules':modules,'local_module_count':len(modules),'unresolved_imports':[]},indent=2)+'\n')
 # Preserve an explicit context diff; extracted theorem bodies are unchanged.
 old_context='import FixedCutBound\nimport Erdos128.BalancedBlowup\nimport Erdos128.RoundingFinal\n'
 new_context='import CutWitness\nimport Erdos128.BalancedBlowup\nimport Erdos128.RoundingFinal\n'
 (H/'BCLTransport-context.patch').write_text(''.join(difflib.unified_diff(old_context.splitlines(True),new_context.splitlines(True),fromfile='PublishedBCL import context',tofile='BCLTransport import context'))+'\ncompletionEnvelope_scale additionally moves from FixedCutBound (import CutScalar) to the same CutWitness context. Full exact extraction ranges/hashes are in extraction.json.\n')
 result={'recorded_utc':datetime.now(timezone.utc).isoformat(),'prior_freezes':checks,'prior_files_verified':sum(x['files_checked'] for x in checks),'copies':copies,'unchanged_inherited_modules':inherited,'local_modules':len(modules),'upstream_repository':'https://github.com/aimir/erdos-128-sparse-halves','upstream_revision':'ba85f319ebb33ec2194ef4c2929a12916329e1e7','declared_toolchain':'leanprover/lean4:v4.30.0','declared_mathlib':'c5ea00351c28e24afc9f0f84379aa41082b1188f','executed_toolchain':'leanprover/lean4:v4.35.0','executed_mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679','unchanged_upstream_modules':upstream_checks,'new_compatibility_patches':None,'inherited_context_patch':'inputs/E9-CutHelpers.patch','BCL_extraction':'extraction.json','E10_control_correction':'Original freeze/raw ambiguous-square result retained. Accepted critic correction bound above. New rejection filter excludes Ambiguous term and elaborated sorry placeholders.'}
 (H/'INPUTS.json').write_text(json.dumps(result,indent=2)+'\n');print({'prior_packets':len(checks),'prior_files':result['prior_files_verified'],'local_modules':len(modules),'all_intact':True})
if __name__=='__main__':main()
