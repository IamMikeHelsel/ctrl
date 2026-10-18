#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent
work=next(q for q in p.parents if (q/'lean-controls/lean-toolchain').is_file())
old=work/'research/pods/2026-10-18/recovery-handoff-02/critic/grip'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
m=old/'artifact-sha256.json'
assert sha(m)=='24771f80d1bec51fc6438e1e82373facc99729595e46b69adc9e309c5b7d2e50'
frozen=json.loads(m.read_text())['files'];r=json.loads((p/'replay-results.json').read_text());checks={}
for n,h in r['source_sha256'].items():
 if n in ['RecoveryPeak','RecoveryPeakWitness']:continue
 rel='fresh/'+n.replace('.','/')+'.lean';q=old/rel
 assert sha(q)==h==frozen[rel],n;checks[n]=h
assert len(checks)==36
out={'passed':True,'prior_critic_manifest_sha256':sha(m),'prior_result_sha256':sha(old/'replay-results.json'),'unchanged_prior_source_count':len(checks),'sha256':checks}
(p/'baseline-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('Matched',len(checks),'prior accepted frozen sources')
