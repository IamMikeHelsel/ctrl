#!/usr/bin/env python3
"""Validate completed independent records; retain full mathematical rejection logs."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
H=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=read(H/'input-check.json')
extra=read(H/'extra-verification.json');assert extra['passed']
vp=H/extra['main_verification'];main=read(vp);fresh=vp.parent
assert sha(vp)==extra['main_verification_sha256']
assert main['passed'] and main['source_hashes_stable'] and not main['development_products_imported']
mods=inputs['complete_local_order']+['Audit']
assert len(main['runs'])==78 and len(main['negative_controls'])==8
expected=['compile-'+x.replace('.','-') for x in mods]+['kernel-'+x.replace('.','-') for x in mods]
assert [r['label'] for r in main['runs'][:70]]==expected
assert all(r['exit']==0 for r in main['runs'][:70])
assert not main.get('audit_parser_repair')
for m,s in main['source'].items():
    assert sha(fresh/s['source'])==sha(H/'builder-copy'/s['source'])==s['sha256']==inputs['declaration_inventory'][m]['source_sha256']
names=set(n for d in inputs['declaration_inventory'].values() for n in d['public'])
assert set(main['declarations_audited'])==set(main['axioms'])==names
assert len(names)==1966
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(v)<=allowed for v in main['axioms'].values())
raw={}
for line in (fresh/'compile-Audit.log').read_text().splitlines():
    if ' depends on axioms: ' in line:
        left,right=line.split(' depends on axioms: ',1)
        raw[left[1:-1]]=[x.strip() for x in right.strip('[]').split(',') if x.strip()]
    elif ' does not depend on any axioms' in line:
        raw[line.split(' does not depend on any axioms',1)[0][1:-1]]=[]
assert raw==main['axioms']
for run in main['runs'][35:70]:
    module=run['command'][1]
    assert (fresh/run['log']).read_text().strip()=='replaying '+module

meaning={
'MissingOrderSquare':'Nonzero raw cost 9/25 differs from normalized cost 1/100. The false equality reduces to False.',
'DirectedEdgeDoubleCount':'The ordered sum is 18/25, not the unordered cost 9/25. The false equality reduces to False.',
'CeilRounding':'The goal still asks for a three-vertex C5 half below 251/400. The context proves every such set has larger cost. This is a false existential goal, not a setup error.',
'BalancedMoment':'The balanced K2 side mass is exactly 1/2. Its strict M-domain inequality reduces to False.',
'WrongHomogeneity':'The raw completion value is 2, whereas the incorrect linear order factor gives 1/5. The claimed equality reduces to False.',
'EmptyPositiveDenominator':'The empty graph order squared is zero. Strict positivity reduces to False.',
'WrongSideScale':'At a nonzero six-vertex profile, the single-y factor differs from the correct y-squared normalization. The false equality reduces to False.',
'QualifiedFalseSquare':'E10.sq is explicitly qualified; the interval [-1,2] square lower bound is zero, so the claimed lower bound 1 reduces to False.'}
records=[]
for run,control in zip(main['runs'][70:],main['negative_controls']):
    name=control['name'];assert name in meaning and run['label']=='reject-'+name
    log=(fresh/run['log']).read_text()
    assert run['exit'] not in (0,124) and 'error: unsolved goals' in log
    assert not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize|Type mismatch|Ambiguous term|\bsorry\b|sorryAx',log)
    if name!='CeilRounding':assert '⊢ False' in log
    else:assert '⊢ ∃ S' in log and 'E10.R * 25 <' in log
    src=fresh/control['source']
    old=H/'builder-copy/evidence/fresh-source-zsj9spb_'/control['source']
    assert sha(src)==sha(old)
    records.append({'name':name,'source':str(src.relative_to(H)),'source_sha256':sha(src),'log':str((fresh/run['log']).relative_to(H)),'log_sha256':sha(fresh/run['log']),'full_log':log,'assessment':meaning[name],'accepted_mathematical_rejection':True})
assert len(extra['runs'])==3 and [r['exit'] for r in extra['runs'][:2]]==[0,0]
assert len(extra['axioms'])==3 and all(set(v)<=allowed for v in extra['axioms'].values())
extra_log=(H/extra['runs'][-1]['log']).read_text()
assert '⊢ False' in extra_log and extra['runs'][-1]['exit'] not in (0,124)
result={'checked_utc':datetime.now(timezone.utc).isoformat(),'passed':True,'main_verification':str(vp.relative_to(H)),'main_verification_sha256':sha(vp),'main_counts':{'compile':35,'kernel':35,'axiom_closures':1966,'semantic_rejections':8,'steps':78},'extra_counts':{'compile':1,'kernel':1,'axiom_closures':3,'semantic_rejections':1,'steps':3},'combined_counts':{'compile':36,'kernel':36,'axiom_closures':1969,'semantic_rejections':9,'steps':81},'audit_exact_name_match':True,'five_primed_names_included':inputs['primed_public_names'],'raw_kernel_log_checks':35,'negative_records':records,'extra_semantic_review':{'scope':'Dropping the positive multiplicity premise from normalized cut descent is false even for the triangle-free C5. A zero-fold blowup has zero internal-cut cost while C5 does not. This does not challenge the correctly stated positive-blowup theorem.','full_rejection_log':extra_log},'extra_verification_sha256':sha(H/'extra-verification.json')}
failed_path=H/'attempts/positive-blowup-control/extra-verification.json'
if failed_path.exists():
    failed=read(failed_path)
    assert not failed['passed'] and len(failed['runs'])==1 and failed['runs'][0]['exit']==1
    failed_log=(H/failed['runs'][0]['log']).read_text()
    assert 'failed to synthesize' in failed_log and 'sorryAx' in failed_log
    result['excluded_failed_critic_attempt']={'verification':str(failed_path.relative_to(H)),'sha256':sha(failed_path),'linked_main_sha256':failed['main_verification_sha256'],'failed_steps':1,'reason':'Missing Decidable synthesis before unfolding a transparent predicate. Not a mathematical rejection and not accepted evidence.','repair':'The same predicate is unfolded before kernel decision; only the extra critic module was rebuilt in a new directory.'}
(H/'final-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('negative_records','extra_semantic_review')},indent=2))
