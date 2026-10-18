#!/usr/bin/env python3
"""Run after main replay; mechanical checks supplement the manual statement review."""
from pathlib import Path
import json,re,hashlib,sys
P=Path(__file__).resolve().parent
work=Path(sys.argv[1]).resolve();d=json.loads((work/'verification.json').read_text());a=(work/'compile-Audit.log').read_text()
assert d['passed'] and d['source_hashes_stable']
assert len(d['declarations_audited'])==len(set(d['declarations_audited']))==102
assert set(d['axioms'])==set(d['declarations_audited'])
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in d['axioms'].values())
mods=d['source']
for mod,entry in mods.items():
 p=P/'builder-copy'/entry['copied'];imports=re.findall(r'^import (.+)$',p.read_text(),re.M)
 for line in imports:
  for dep in line.split(): assert dep=='Mathlib' or dep in mods,(mod,dep)
assert len(mods)==12
required=['half_from_squared_certificates','normalized_certificates','normalized_cost_extension','mass_extension','isFractionalHalf_extendLarge','largeGraph_cliqueFree','exists_affine_profile','structure Erdos128.OrientedBCLCut','def Erdos128.IsFractionalHalf','def Erdos128.HasNormalizedFractionalHalfBoundQ']
assert all(n in a for n in required)
assert len(d['runs'])==30
assert sum(r['label'].startswith('compile-') and r['exit']==0 for r in d['runs'])==13
assert sum(r['label'].startswith('kernel-') and r['exit']==0 for r in d['runs'])==13
for r in d['runs']:
 if r['label'].startswith('reject-'):
  out=(work/r['log']).read_text()
  assert r['exit'] not in (0,124) and 'unsolved goals' in out
  assert not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize',out)
result={'passed':True,'verification_sha256':hashlib.sha256((work/'verification.json').read_bytes()).hexdigest(),'audit_log_sha256':hashlib.sha256(a.encode()).hexdigest(),'public_closures_checked':102,'axiom_union':sorted({x for v in d['axioms'].values() for x in v}),'local_source_modules':len(mods),'no_local_imports_outside_rebuilt_closure':True,'modules':{n:v['public_theorems'] for n,v in mods.items()},'kernel_signature_manual_review':'Actual endpoint and printed definitions inspected; no hidden profile, moment, density or maximum-cut premise. Supplied cut carries explicit BCL internal_bound.','audit_scope':'Every declared public theorem identified by replay plus main endpoint transitive dependencies; not full Mathlib source rebuild.','main_run_counts':{'compiles':13,'kernels':13,'mathematical_rejections':4}}
(P/'statement-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
