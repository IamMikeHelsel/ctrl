from pathlib import Path
import json,hashlib,datetime
B=Path(__file__).resolve().parent;R=B.parents[4];S=B.parent/'builder-05'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fresh=json.loads((B/'fresh-result.json').read_text())
clients=json.loads((B/'client-result.json').read_text())
counter=json.loads((B/'counter-result.json').read_text())
oracle=json.loads((B/'integer-oracle-result.json').read_text())
assert all(x['status']=='PASS' for x in [fresh,clients,counter,oracle])
assert fresh['modules']==25 and fresh['kernel_replays']==25
assert clients['positive_client_theorems']==22 and clients['negative_clients']==9
assert counter['proved_counter_witnesses']==9 and counter['audited_local_declarations']==485
for rel,rec in fresh['preservation'].items():
    d=R/rel;assert sha(d/'SHA256SUMS')==rec['manifest_sha256']
    for line in (d/'SHA256SUMS').read_text().splitlines():
        h,f=line.split('  ',1);assert sha(d/f)==h,(rel,f)
for p in (B/'source').glob('*.lean'):assert sha(p)==sha(S/p.name)
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
result={'decision':'ACCEPT bounded actual split-signature certificate','evidence_grade':'A for this named formal and independent replay gate, not publication quality or probability','completed_utc':now,'builder_manifest_sha256':sha(S/'SHA256SUMS'),'fresh_local_modules':25,'separate_kernel_replays':27,'new_reviewer_theorems':22,'proved_false_claim_negations':9,'negative_clients_rejected':9,'all_local_declarations_audited':485,'permitted_axioms':['propext','Classical.choice','Quot.sound'],'preserved_prior_manifests':10,'prior_entries_checked':657,'builder_entries_checked':120,'inherited_sources_unchanged':21,'oracle_actual_basis_actions':128,'oracle_matrix_entry_equalities':1507328,'oracle_matrix_identities':92,'oracle_gaussian_integer_pair_tests':32,'oracle_omitted_D_kernel_vectors':64,'claims':['Actual complement action derived from creation/contraction','U=I+KD is invertible with U^T/2 on both sides','U^T K U=2D and exact64+64 indexed cardinalities','Actual complex Kc has Uc^H Kc Uc=2Dc and both inverse identities'],'limitations':['Explicit indexed congruence, not a separate abstract inertia theorem or arbitrary Fin64 enumeration','Standard algebra; originality and venue fit unassessed','No GU physical validation or field equation','Source-specific operator and variation choices remain undefined in this formalization','Pinned public dependency products, compiler products and hardware remain trusted; leanchecker is not an independent kernel implementation'],'recommendation':'STOP source-specific GU expansion; reopen only for a precisely supplied definition or separately justified formalization target','shared_usage_at_start':64,'shared_usage_observed_2026_10_18_090923_UTC':65,'credits_observed':'66235.3330170000','per_agent_usage':'unavailable'}
(B/'result.json').write_text(json.dumps(result,indent=2)+'\n')
(B/'REPORT.txt').write_text(f'''Independent GU builder-05 review
Completed {now}

Decision: ACCEPT the bounded actual split-signature certificate.
Grade: A for this named verification gate. This is not a publication or physics grade.

The exact result
For the existing ordered product K=N0*N1*...*N6 in the actual exterior basis,
K e_T=(-1)^(sum over i in T of (7-i)) e_(T complement).
The proof derives this action from actual creation and contraction operators.
It does not assume the target matrix action.

Let D be diagonal: +1 when coordinate 0 is absent, -1 when it is present.
U=I+KD satisfies U^T U=UU^T=2I and U^T K U=2D. Both inverse equations use U^T/2.
There are exactly 64 indices in each half. The congruence has zero off-diagonal
entries and diagonal entries +2 and -2. Thus grouping these explicit index sets
gives diag(2I64,-2I64). An arbitrary Fin64 reindexing is not part of the formal claim.

The entrywise complex extension uses the same actual Kc. It proves
Uc^H Kc Uc=2Dc and both inverse equations with Uc^H/2, where H is conjugate
transpose. The existing Kc is Hermitian. The (64,64) form is on the 128-dimensional
spinor space; it is distinct from the (7,7) form on the 14 generators.

Independent verification
All 25 local source modules were rebuilt from fresh copied source. The builder
cache and root project cache were excluded. Lean 4.35.0 and mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679 were unchanged. The actual mathlib checkout
was clean. Only pinned public dependency products were reused.

There are 22 new client theorems, including actual eigen-column, sign, diagonal,
off-diagonal, inverse and count probes. Nine false clients were rejected with
unsolved mathematical goals. Separately, nine client theorems prove the negations
of those exact false claims, so a weak tactic alone cannot explain the rejection.
The final audit covers all 485 local declarations, including private helpers.
Only propext, Classical.choice and Quot.sound occur. No local axiom or unsafe
route was accepted. All 27 separate leanchecker replays passed: the 25 source
modules plus both reviewer client modules. There were no failed positive builds.

The independent integer oracle uses sorted wedge tuples, insertion permutations
and contraction positions. It imports no builder Python code or result data.
It checks all 128 actual basis actions and 1,507,328 matrix-entry equalities across
92 identities. It also checks 32 sesquilinear pairings with exact Gaussian-integer
vectors. Six concrete mutations give the wrong values. Omitting D produces a
matrix that kills 64 disjoint, nonzero paired vectors; it is not a basis change.
These exact finite checks supplement the proof. They are not physical evidence.

Preservation
The builder manifest is
{result['builder_manifest_sha256']}
All 120 entries match. Ten prior frozen manifests and their 657 entries match
before and after review. All 21 inherited source files match their accepted
predecessors. This reviewer changed only critic-05. The cache is excluded from
this review's frozen manifest; copied source, scripts, logs and reports are kept.

Boundary and next step
This formalizes standard algebra tied to the actual constructed matrices. It
proves neither publication novelty nor a physical claim of Geometric Unity.
The accepted computation does not establish uniqueness under Spin invariance;
full vector-adjoint assumptions are a different and stronger condition.

Stop source-specific GU expansion here. To proceed, fix the normalized Phi
operators, brackets/projections, domains, Bianchi assumptions and variation data.
The action is already displayed in the source; do not say the action is absent.
The intended scalar-conjugation convention remains a source question.
NEXT-GATE.txt points to the precise, corrected, unsent question list. I checked
that saved list and review record; I did not repeat the online source search.
A standalone formalization paper still needs human value/novelty review and a
clear reuse or library-integration target.

Trust boundary
The compiler, pinned dependency products and hardware remain trusted.
leanchecker supplies a separate replay process, not a second kernel implementation.
No paid API, new subagent, submission, external message, billing change, Git
operation, manuscript edit or shared-state edit was performed by this reviewer.
''')
files=sorted(p for p in B.rglob('*') if p.is_file() and 'cache' not in p.relative_to(B).parts and p.name!='SHA256SUMS')
(B/'SHA256SUMS').write_text(''.join(sha(p)+'  '+str(p.relative_to(B))+'\n' for p in files))
for line in (B/'SHA256SUMS').read_text().splitlines():
    h,f=line.split('  ',1);assert sha(B/f)==h
print(json.dumps({'manifest_sha256':sha(B/'SHA256SUMS'),'files':len(files),'result':result},indent=2))
