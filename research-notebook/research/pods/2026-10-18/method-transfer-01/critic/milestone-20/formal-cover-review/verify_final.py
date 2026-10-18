#!/usr/bin/env python3
"""Bind independently produced execution evidence; do not accept mere exit failure."""
from pathlib import Path
import json,hashlib,re,datetime
D=Path(__file__).resolve().parent;ROOT=next(p for p in D.parents if (p/'lean-controls').is_dir())
B=D/'builder-copy';original=ROOT/'research/pods/2026-10-18/method-transfer-01/erdos/formal-cover-10'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mp=D/(D/'main-replay-path.txt').read_text().strip();v=json.loads(mp.read_text())
ep=D/'extra-evidence/verification.json';e=json.loads(ep.read_text())
assert v['passed'] and e['passed'] and v['source_hashes_stable']
assert len(v['runs'])==29 and len(e['runs'])==4
assert all(r['exit']==0 for r in v['runs'] if not r['label'].startswith('reject-'))
assert all(r['exit']!=0 and r['exit']!=124 for r in v['runs'] if r['label'].startswith('reject-'))
assert len(v['axioms'])==1821 and len(e['axioms'])==1
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(a)<=allowed for a in [*v['axioms'].values(),*e['axioms'].values()])
decls=json.loads((D/'input-check.json').read_text())['declarations']
assert set(v['axioms'])==set(decls)==set(v['declarations_audited'])
assert e['main_verification_sha256']==sha(mp)
assert len([r for r in v['runs'] if r['label'].startswith('kernel-')])==11
interpretations={
 'MissingChild':'22/25 is outside the left root child [767/1000,4/5].',
 'WrongBoundary':'The shared 4/5 point is in neither child if both inequalities are strict.',
 'FalseSquareBound':'The square of [-1,2] has lower endpoint 0, not 1.',
 'WrongReciprocalOrder':'1/2 is not in the inverted pair (1,1/2).',
 'WrongSlope':'The proved matched-point positive high certificate contradicts theta0 success.',
 'WrongTarget':'The formal all-slope obstruction contradicts the complete selector at .025.',
 'VariableSlopeCancellation':'The displayed mean is 1/4, not zero.',
 'FalseUnguardedReciprocal':'c=1/2 belongs to [-1,1], but reciprocal 2 is outside naive inverse (1,-1); safe is false.'}
neg=[]
for n in v['negative_controls']:
 log=(mp.parent/n['log']).read_text();assert 'unsolved goals' in log
 if n['name']=='FalseSquareBound':
  assert 'Ambiguous term' in log and 'sorry () = 1' in log
  continue
 assert not re.search(r'Unknown identifier|unknown constant|unknown module|unexpected token|failed to synthesize|Type mismatch|TIMEOUT|Ambiguous term|\bsorry\b',log)
 neg.append({'name':n['name'],'meaning':interpretations[n['name']],'source':str((mp.parent/n['source']).relative_to(D)),'source_sha256':sha(mp.parent/n['source']),'log':str((mp.parent/n['log']).relative_to(D)),'log_sha256':sha(mp.parent/n['log']),'goal_output':log})
for name,key in [('FalseSquareBoundRepaired','FalseSquareBound'),('FalseUnguardedReciprocal','FalseUnguardedReciprocal')]:
 log=(ep.parent/('reject-'+name+'.log')).read_text();assert 'unsolved goals' in log
 assert not re.search(r'Unknown identifier|unknown constant|unknown module|unexpected token|failed to synthesize|Type mismatch|TIMEOUT|Ambiguous term|\bsorry\b',log)
 neg.append({'name':name,'meaning':interpretations[key],'source':'extra-evidence/'+name+'.lean','source_sha256':sha(ep.parent/(name+'.lean')),'log':'extra-evidence/reject-'+name+'.log','log_sha256':sha(ep.parent/('reject-'+name+'.log')),'goal_output':log})
assert len(neg)==8
(D/'negative-review.json').write_text(json.dumps({'scope':'Six valid original controls plus qualified square replacement and independent reciprocal safety control; not eight full source mutations','rejected_raw_evidence':'attempts/ambiguous-square-control/assessment.json','controls':neg},indent=2)+'\n')
m=json.loads((original/'artifact-sha256.json').read_text());assert sha(original/'artifact-sha256.json')=='7ec490ffe083b7db4767105ef8a4ff5e369e99f46905760f72673a288ac466b4'
for rel,h in m['files'].items():assert sha(original/rel)==h==sha(B/rel),rel
prov=json.loads((B/'INPUTS.json').read_text());nold=0
for item in prov['prior_freezes']:
 p=ROOT/item['manifest'];assert sha(p)==item['sha256'];old=json.loads(p.read_text())['files']
 for rel,h in old.items():assert sha(p.parent/rel)==h
 nold+=len(old)
for item in prov['copies']:assert sha(ROOT/item['original'])==item['sha256']==sha(B/item['copy'])
pres={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'E10_manifest_sha256':sha(original/'artifact-sha256.json'),'E10_original_and_copied_entries':len(m['files']),'prior_freeze_entries':nold,'all_hashes_stable':True,'executed_pins_unchanged':True}
(D/'final-preservation.json').write_text(json.dumps(pres,indent=2)+'\n')
index={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'main':{'path':str(mp.relative_to(D)),'sha256':sha(mp),'raw_steps':len(v['runs']),'accepted_steps':28,'compiles':11,'kernel_checks':11,'axiom_closures':len(v['axioms']),'valid_negative_controls':6,'invalid_control':'FalseSquareBound','raw_passed_true_is_not_accepted_for_that_control':True},'extra':{'path':str(ep.relative_to(D)),'sha256':sha(ep),'steps':len(e['runs']),'compiles':1,'kernel_checks':1,'axiom_closures':1,'negative_controls':2},'combined':{'attempted_steps':33,'accepted_steps':32,'invalid_preserved_attempts':1,'compiles':12,'kernel_checks':12,'axiom_closures':1822,'valid_negative_controls':8},'accepted_evidence_passed':True,'forbidden_axioms':[],'failure_provenance':'attempts/ambiguous-square-control/assessment.json','note':'Main 1821 closures include 1744 generated node/root declarations. Extra checks reuse this review fresh closure, never builder proof products. The raw square-control false positive remains unchanged and is explicitly excluded.'}
(D/'FINAL-INDEX.json').write_text(json.dumps(index,indent=2)+'\n')
print(json.dumps(index,indent=2))
