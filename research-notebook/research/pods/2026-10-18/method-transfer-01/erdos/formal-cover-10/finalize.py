#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 vs=sorted((H/'evidence').glob('fresh-source-*/verification.json'),key=lambda p:p.stat().st_mtime);vpath=vs[-1];v=json.loads(vpath.read_text());assert v.get('passed'),v.get('stopped_at');assert v['source_hashes_stable']
 for m,s in v['source'].items():assert sha(H/s['source'])==s['sha256']
 attempts=[]
 for p in sorted(H.glob('attempt-*/run.json')):
  d=json.loads(p.read_text())
  if 'module' in d:attempts.append({'directory':str(p.parent.relative_to(H)),**d})
 failures=[x for x in attempts if x['exit']!=0]
 (H/'development-attempts.json').write_text(json.dumps(attempts,indent=2)+'\n')
 (H/'FAILURES.txt').write_text('PRESERVED DEVELOPMENT FAILURES\n\n'+''.join(f"{x['directory']}: {x['module']}, exit {x['exit']}. Exact source, compiler log and run metadata retained.\n" for x in failures)+'\nThe first acquisition attempt incorrectly looked for E9/Erdos128/WeightedGraph.lean; the unchanged source was in E9/upstream-original/Erdos128/. No old file was changed. The first generator draft used method name moment while the frozen JSON uses free_moment. That failed before writing a generated proof; the exact node is preserved in the unchanged JSON. The generated root first needed an explicit rational normalization of 0/1 and I; this failed compile is retained. No mathematical region, target or certificate was changed.\n\nThe fresh replay retains every deliberate mathematical rejection. These are controls, not unresolved proof obligations.\n')
 (H/'CLAIMS.txt').write_text('E10 CLAIMS\n\nProved in Lean under the existing local pin: the complete universal rational selector at R=251/10000 and I=2/47, for 1/2<=c<=1 and 0<=j<=I. Its endpoint has only those parameter bounds as hypotheses. All three disjuncts have their intended domains; the moment disjunct supplies one common rational slope and the unchanged E9 A/H certificates.\n\nProved supporting results: generic interval expression soundness; completion monotonicity and join; full closed split coverage; all 872 frozen E5 leaf checks; analytic low/high exteriors; exact .025 all-slope obstruction; matched .0251 slope-needed control.\n\nNot claimed: a new graph endpoint, BCL-all-orders composition, integral rounding, a new constant search, novelty, best-known status, or a graph counterexample at .025. This packet is submitted for independent acceptance. Builder verification is not acceptance.\n')
 counts=json.loads((H/'generated-data.json').read_text())['methods']
 fresh=f"{vpath.relative_to(H)}"
 (H/'REPORT.txt').write_text(f'''E10 FORMAL SELECTOR — BUILDER FREEZE

The complete rational selector at R=251/10000=.0251 and I=2/47 is proved.
The endpoint has only 1/2<=c<=1 and 0<=j<=I as variable hypotheses. It gives
uniform U, valid-domain completion Q, or one common rational slope with
E9's exact low/high certificates. No checked-data premise remains.

The interval evaluator and closed split rules are proved generically. The
unchanged E5 tree is discharged by 1743 node proofs: 872 leaves comprising
53 uniform, 250 completion and 569 moment cells. All rational leaf checks
run in the kernel. Analytic exteriors include c=1/2 and c=1. Shared cell
boundaries are covered. Completion agrees at its join. Positive reciprocal
reversal and zero-crossing square bounds are proved, not assumed.

Fresh verification: {len(v['source'])+1} source modules compiled, {len(v['declarations_audited'])} public theorem
axiom closures passed the allowlist, {len(v['source'])+1} separate leanchecker module checks
passed, and {len(v['negative_controls'])} false mathematical controls were rejected. All copied sources
match the inputs. Exact evidence: {fresh}.
The only allowed axioms are propext, Classical.choice and Quot.sound.
No native decision or unsafe proof mechanism is used.

The .025 changed-target control is a theorem, not just a failed table:
at c=133/160,j=71/1880 both U and Q fail, while H(L)>0 for every rational L.
The matched .0251 point requires the slope change: U,Q and theta0 fail,
while theta1 satisfies both certificates. Additional controls reject an
omitted root child, an open shared boundary, a false square lower bound,
reversed reciprocal endpoints and variable-slope mean cancellation (an arithmetic control, not a graph).

All 496 files in ten prior builder freezes remain hash-identical. The three
attributed upstream modules and accepted E8/E9 sources are unchanged.
Execution uses the existing Lean4.35/mathlib pin, not an upstream4.30 replay.
{len(failures)} failed development compilations and their sources/logs are retained.

This is the scalar selector gate. The actual finite-graph U/Q/M composition,
external BCL all-orders interface and integral floor-half rounding remain
later work. No novelty or best-known claim follows. Independent acceptance
is pending; the builder does not accept its own result.
''')
 (H/'CONTROLS.txt').write_text('CONTROLS\n\nSelectorControls.lean proves an all-slope changed-target counterexample at .025 and the matched slope-needed point at .0251. The first is a scalar relaxation obstruction, not a graph counterexample. It also checks the four parameter-domain corners, completion join, middle denominator signs, square crossing zero, reciprocal order, closed split boundary and variable-slope failure.\n\nFresh replay compiles seven deliberately false claims. MissingChild uses the actual omitted right root region: c=22/25 is not in [767/1000,4/5]. WrongBoundary makes the shared root c=4/5 boundary strict on both sides. FalseSquareBound claims lower bound 1 for the square of [-1,2], which contains 0. WrongReciprocalOrder fails membership after using unswapped endpoints. WrongSlope claims theta0 succeeds at the matched point. WrongTarget claims the impossible full .025 selector at the obstruction. VariableSlopeCancellation claims a positive weighted mean is zero. This two-point arithmetic control is not asserted to be a graph. Each rejection must be an unsolved mathematical goal, not a parser, identifier, typeclass or type mismatch failure.\n')
 (H/'REMAINING.txt').write_text('REMAINING\n\nIndependent review of this freeze. Then root may choose a separate graph composition milestone: map U to the actual uniform side profile; map Q to the completion theorem in its correct c>=3/4 domain; map M to the accepted E9 finite-graph bridge, using c<1 to establish y>1/2. Retain the external hBCL contract, all-orders blowup descent, empty graph case and integral floor-half rounding. None is silently asserted by this scalar theorem.\n')
 (H/'FINAL-INDEX.json').write_text(json.dumps({'status':'frozen-for-independent-review','endpoint':'E10.universal_selector','exact_statement':'EXACT-STATEMENT.txt','proof_map':'PROOF-MAP.txt','evidence':fresh,'evidence_sha256':sha(vpath),'source_modules':list(v['source']),'public_theorem_audits':len(v['declarations_audited']),'kernel_modules':len(v['source'])+1,'negative_controls':len(v['negative_controls']),'prior_preserved_files':496,'development_failures':len(failures)},indent=2)+'\n')
 files={}
 for p in sorted(H.rglob('*')):
  if not p.is_file() or p.name=='artifact-sha256.json' or '__pycache__' in p.parts or any(s in p.name for s in ['.olean','.ilean','.ir']):continue
  files[str(p.relative_to(H))]=sha(p)
 manifest={'frozen_utc':datetime.now(timezone.utc).isoformat(),'scope':'E10 complete universal rational .0251 selector, generic interval soundness, closed tree coverage, analytic exteriors and fresh proof evidence; pending independent acceptance','excluded':'Compiled Lean products and Python cache. Build product hashes are recorded in verification.json.','files':files}
 p=H/'artifact-sha256.json';p.write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'manifest':str(p),'sha256':sha(p),'files':len(files),'bytes':sum((H/x).stat().st_size for x in files),'verification':fresh,'verification_sha256':sha(vpath),'audits':len(v['declarations_audited']),'kernels':len(v['source'])+1,'controls':len(v['negative_controls'])},indent=2))
if __name__=='__main__':main()
