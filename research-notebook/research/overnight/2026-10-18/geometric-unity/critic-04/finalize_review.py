from pathlib import Path
import json,hashlib,subprocess,datetime,sys
D=Path(__file__).resolve().parent
r=json.loads((D/'lean-review.json').read_text());a=json.loads((D/'full-audit-review.json').read_text());e=json.loads((D/'exact-review.json').read_text())
assert r['status']==a['status']==e['status']=='PASS'
assert r['fresh_modules']==21 and r['client_theorems']==19 and r['negative_controls']==7 and r['kernel_checks']==22
assert len([s for s in r['steps'] if s['name'].startswith('kernel-') and s['code']==0])==22
assert len([s for s in r['steps'] if s['name'].startswith('fresh-') and s['code']==0])==21
assert a['all_local_declarations_audited']==390 and all(a['module_counts'].values())
subprocess.run([sys.executable,str(D/'check_preservation.py'),'preservation-after.json'],check=True)
p=json.loads((D/'preservation-after.json').read_text());assert p==json.loads((D/'preservation-before.json').read_text())
if not (D/'attempts/lean-review-before-full-audit.json').exists():
 (D/'attempts/lean-review-before-full-audit.json').write_bytes((D/'lean-review.json').read_bytes())
r['all_local_declarations_audited']=a['all_local_declarations_audited'];r['module_audit_counts']=a['module_counts']
r['full_audit_source']='full-audit-review.json'
r['audit_scope_correction']='Initial ReviewClient import did not import OrderControls. An explicit full-module audit was run and passed. Original result is preserved in attempts/lean-review-before-full-audit.json.'
if not any(s['name']=='FullAudit' for s in r['steps']):r['steps'].append({'name':'FullAudit','code':0,'seconds':a['seconds'],'command':a['command']})
(D/'lean-review.json').write_text(json.dumps(r,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
decision={'decision':'ACCEPT','grade':'A for the bounded proof evidence gate; no novelty or physics grade','scope':'Actual complex tensor algebra equivalence and conjugate-transpose bridge under the explicitly declared conjugate-linear bar','builder_manifest_sha256':'861cd093c525217d7f9f04dbee0ff22889efd541e746bc7a82eeea9a20c4a8c9','fresh_local_modules':21,'independent_client_theorems':19,'all_local_declarations_audited':390,'separate_kernel_replays':22,'false_controls':7,'mixed_exact_examples':48,'mixed_exact_products':24,'explicit_matrix_unit_examples':128,'frozen_manifests_checked':9,'frozen_files_checked':561,'repair_required_in_candidate':False,'reviewer_harness_repairs_preserved':True,'Lean_signature_proof':False,'global_spin_group_proof':False,'GU_operator_selection':False,'physics_validation':False,'publication_novelty_established':False,'next_gate':'Actual K complement sign and explicit invertible 64-plus/64-minus congruence','completed_utc':now}
(D/'decision.json').write_text(json.dumps(decision,indent=2)+'\n')
report='''ACCEPT — actual complex matrix equivalence and conjugate-transpose bridge
Independent evidence gate accepted within the declared algebraic scope.
18 October 2026 UTC

The source constructs an actual complex algebra equivalence
  rho : C tensor_R Cl(7,7) -> M_128(C)
with rho(z tensor a)=z*ofReal(realrho(a)). It supplies an inverse for every
complex matrix. Genuine matrix multiplication is proved separately from the
finite-product linear maps used to construct that inverse.

For every element x of that actual tensor algebra, it proves
  rho(bar x) = Kc * conjugateTranspose(rho(x)) * Kc.
Kc is the coefficient extension of the accepted ordered product of the seven
actual negative generators. Neither faithfulness nor the adjoint bridge is an
extra premise. The form is Hermitian and its square is the identity. SCOPE.txt
records the construction audit and source boundary.

Fresh proof review
All 21 frozen local modules were rebuilt with the pinned Lean4.35.0 toolchain.
Nineteen independent client theorems passed. They cover unique matrix preimages,
actual product coordinates, mixed tensors, conjugated scalars, inverse adjoints,
noncommuting preimages, non-vacuity and the exact skew-condition transport.
All 390 local declarations, including private helpers, passed the full-closure
axiom audit. No local axiom or unsafe declaration occurs. Dependencies are
limited to propext, Classical.choice and Quot.sound. All 22 separate leanchecker
replays passed. Seven false clients failed for mathematical reasons; none was
accepted as a negative control due to a missing import or identifier.

The independent exact check used arbitrary-precision Gaussian integers and a
separate tuple-wedge implementation. It checked 48 mixed complex examples,
24 products, 128 explicit matrix-unit images, and a dense 128-by-128 complex
matrix involution. It rejected ordinary transpose on iI, conjugating the forward
scalar map, pointwise multiplication and unreversed product order. These finite
checks supplement, rather than replace, the general Lean result.

Preservation and trust
Nine pinned manifests and their 561 listed files were checked before and after.
Seventeen inherited real sources and the inherited complex bar match their
accepted sources byte-for-byte. The Mathlib checkout is clean at
56a005855ea17e0b0958f73ec801ae140b0a1679. No local project or builder cache was
used. Pinned prebuilt dependencies, compiler products and hardware remain
trusted inputs. No candidate source was edited.

Reviewer repairs were retained. An initial closure preflight omitted the separate
OrderControls module. Two reviewer-client attempts then needed a corrected
rewrite and smaller proof expression to avoid kernel recursion depth failures.
The complete source rebuild had already passed. The final clients used the
unchanged fresh closure. An explicit full-module environment audit then included
OrderControls; the initial import-only audit result remains in attempts/. These
were reviewer harness/client issues, not defects in the frozen candidate.

Decision and next test
No candidate repair is required. The next concrete gate is the actual K
complement action and an explicit invertible congruence with 64 positive and
64 negative directions. NEXT-GATE.txt gives a sign formula, checked in all 128
exact coordinate cases, and a proof sketch. It is not yet a Lean signature proof.

This is standard algebra formalization. The chosen bar conjugates complex
scalars; the source-convention question in critic-01 remains open. No global
Spin-group claim, Phi choice, action variation, field equation, physical
prediction or publication novelty follows from this gate. The source correction
that action (9.4) already exists still applies. Root owns repository integration.
'''
(D/'report.txt').write_text(report)
# Source/check records are retained; compiled caches are excluded from the freeze.
paths=sorted(p for p in D.rglob('*') if p.is_file() and 'cache' not in p.relative_to(D).parts and '__pycache__' not in p.relative_to(D).parts and p.name!='SHA256SUMS')
(D/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(D))+'\n' for p in paths))
print(json.dumps({'decision':'ACCEPT','files':len(paths),'manifest_sha256':hashlib.sha256((D/'SHA256SUMS').read_bytes()).hexdigest(),'completed_utc':now}))
