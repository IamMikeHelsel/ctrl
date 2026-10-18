#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,re
H=Path(__file__).resolve().parent;ROOT=next(p for p in H.parents if (p/'lean-controls').is_dir());BASE=H.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 old=json.loads((H.parent/'finite-graph-09/INPUTS.json').read_text())['prior_freezes']
 old.append({'manifest':'research/pods/2026-10-18/method-transfer-01/erdos/finite-graph-09/artifact-sha256.json','sha256':'ac731e5eac922097a38b58eacdf6a062c6f4d495f9a24903376351f391d2eb79'})
 checks=[]
 for item in old:
  p=ROOT/item['manifest'];assert sha(p)==item['sha256'];data=json.loads(p.read_text())
  for rel,h in data['files'].items():assert sha(p.parent/rel)==h,(p,rel)
  checks.append({'manifest':item['manifest'],'sha256':sha(p),'files_checked':len(data['files']),'all_match':True})
 paths={'AGENTS.md':ROOT/'AGENTS.md','CHARTER.txt':BASE/'CHARTER.txt','formal-cover-card.txt':BASE/'root-review/FORMAL-COVER-CARD.txt','statement-gate.txt':BASE/'critic/milestone-14/formal-cover-gate/REPORT.txt','accepted-E9-interface.txt':BASE/'critic/milestone-15/finite-graph-review/NEXT-E10-INTERFACE.txt','E9-review.txt':BASE/'critic/milestone-15/finite-graph-review/REPORT.txt','E5-PROOF.txt':H.parent/'free-slope-05/PROOF.txt','executed-lean-toolchain':ROOT/'lean-controls/lean-toolchain','executed-lake-manifest.json':ROOT/'lean-controls/lake-manifest.json'}
 copies=[]
 for cp,p in paths.items():
  dst=H/'inputs'/cp;shutil.copyfile(p,dst);copies.append({'copy':str(dst.relative_to(H)),'original':str(p.relative_to(ROOT)),'sha256':sha(p)})
 mods=[]
 for mod in ['Erdos128/WeightedGraph','Erdos128/CubicNeighborhood','Erdos128/OneStepSaving','WeightedProfiles','SquareCertificate']:
  src=H.parent/'finite-graph-09'/('upstream-original' if mod.startswith('Erdos128/') else '')/(mod+'.lean')
  dst=H/(mod+'.lean');assert sha(src)==sha(dst)
  mods.append({'module':mod.replace('/','.'),'original':str(src.relative_to(ROOT)),'copy':str(dst.relative_to(H)),'sha256':sha(dst),'byte_identical':True,'imports':re.findall(r'^import (.+)$',dst.read_text(),re.M)})
 for name in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
  src=H.parent/'finite-graph-09/upstream-original'/name;dst=H/'inputs'/('upstream-'+name);shutil.copyfile(src,dst);copies.append({'copy':str(dst.relative_to(H)),'original':str(src.relative_to(ROOT)),'sha256':sha(src)})
 result={'recorded_utc':datetime.now(timezone.utc).isoformat(),'prior_freezes':checks,'prior_files_verified':sum(x['files_checked'] for x in checks),'copies':copies,'unchanged_dependencies':mods,'upstream_repository':'https://github.com/aimir/erdos-128-sparse-halves','upstream_revision':'ba85f319ebb33ec2194ef4c2929a12916329e1e7','declared_toolchain':'leanprover/lean4:v4.30.0','declared_mathlib':'c5ea00351c28e24afc9f0f84379aa41082b1188f','executed_toolchain':'leanprover/lean4:v4.35.0','executed_mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679','dependency_patches':None,'certificate_sha256':sha(H/'inputs/certificate.json')}
 (H/'INPUTS.json').write_text(json.dumps(result,indent=2)+'\n');print({'prior_packets':len(checks),'prior_files':result['prior_files_verified'],'all_intact':True})
if __name__=='__main__':main()
