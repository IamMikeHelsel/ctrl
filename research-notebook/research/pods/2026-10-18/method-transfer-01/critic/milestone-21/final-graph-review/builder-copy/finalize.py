#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 vp=max((H/'evidence').glob('fresh-source-*/verification.json'),key=lambda p:p.stat().st_mtime);v=json.loads(vp.read_text());assert v.get('passed') and v['source_hashes_stable']
 for m,s in v['source'].items():assert sha(H/s['source'])==s['sha256']
 inherited=json.loads((H/'INPUTS.json').read_text());assert inherited['prior_files_verified']==654
 attempts=[]
 for p in sorted(H.glob('attempt-*/run.json')):
  x=json.loads(p.read_text())
  if 'module' in x:attempts.append({'directory':str(p.parent.relative_to(H)),**x})
 fails=[x for x in attempts if x['exit']!=0];(H/'development-attempts.json').write_text(json.dumps(attempts,indent=2)+'\n')
 (H/'FAILURES.txt').write_text('PRESERVED FAILURES\n\n'+''.join(f"{x['directory']}: {x['module']}, exit {x['exit']}. Exact source/log/run metadata retained.\n" for x in fails)+'\nThe new completion_agrees proof first omitted introductions in an iff proof and used rw under a dependent Decidable if. The repair adds the introductions and uses simp only for that exact iff. No statement or inherited proof changed.\n\nThe first fresh Audit failed because the inherited runner truncated apostrophes in five public rounding-lemma names. The original runner, declaration list, Audit source, compile log and failed verification are retained. The corrected parser supports primed names and rejects duplicate parsed names. After checking every copied source hash and every successful proof-module build, the audit-only repair regenerated/compiled Audit in the same fresh workspace. It then audited all public declarations and separately checked every module with leanchecker. No development products entered the fresh workspace. The canonical replay.py also supports a complete fresh run with no arguments.\n\nThe original E10 ambiguous-square raw result remains in its untouched packet. This packet binds the accepted critic correction and uses qualified E10.sq with stricter rejection filters. All eight new expected rejections are mathematical unsolved goals; ambiguity and placeholder failures are excluded.\n')
 (H/'CLAIMS.txt').write_text('E11 CLAIMS\n\nProved in Lean, conditional on exactly the transparent BCLEventual input: every finite triangle-free simple graph G on n vertices has a vertex set of cardinality floor(n/2) spanning at most (251/10000)n^2 unordered edges. Empty, odd and even orders are included. No regularity, maximum-cut optimality, stronger cut bound or desired-cost premise is added.\n\nThe actual oriented-cut endpoint derives its scalar domain and uses actual uniform, completion or moment profiles. The all-orders endpoint uses the unchanged positive-blowup cut descent, twin averaging and floor rounding. Explicit even and odd cut-level examples do not assume BCLEventual.\n\nNot proved: BCLEventual itself; the conjectural 1/50 coefficient; novelty or best-known status. The external stronger-cut comparison is unused. This is formal closure of the already written E5 route. Independent acceptance is pending; the builder does not accept its own work.\n')
 report=f'''E11 FINAL CONDITIONAL GRAPH ENDPOINT — BUILDER FREEZE

The actual all finite graph .0251 floor-half endpoint is proved in Lean:
 Erdos128.FinalGraph.sparse_half_251_10000.
For each finite triangle-free simple graph on n vertices, it gives S with
|S|=floor(n/2) and e(S)<=(251/10000)n^2. BCLEventual is the only external
mathematical hypothesis. It is the exact transparent eventual 2/47 cut
proposition; this packet does not prove it. No new graph premise is added.

The proof derives c,j from an actual oriented cut. It assembles actual U,
Q and M profiles, with correct completion domain, n^2 homogeneity, shared
c=4/5 boundary, and one common moment slope. Empty and balanced cases are
explicit. Positive blowup/descent removes the eventual-order threshold;
twofold blowup handles parity; the unchanged rounding theorem gives floor.

The complete recorded closure has 34 local modules, plus Audit. All 31
inherited modules retain their bytes; all 11 upstream Erdos128 modules also
match the pinned source. No full LowDensityConstruction, PublishedBCL or
FixedCutBound import is present. The BCL transport/homogeneity extraction
preserves its bodies exactly and records its import-context changes.

Fresh evidence:34 proof modules built from copied sources; corrected Audit
compiled; {len(v['declarations_audited'])} public theorem axiom closures passed;35 separate kernel
checks passed; {len(v['negative_controls'])} false mathematical controls were rejected. The allowed
axioms are propext, Classical.choice and Quot.sound. No unsafe or native
proof shortcut is used. Evidence: {vp.relative_to(H)}.

One audit-harness repair is fully preserved. Five primed rounding names
were initially truncated. The corrected parser handles apostrophes and
checks uniqueness. Only Audit was rebuilt after all unchanged fresh proof
module hashes/builds were checked. The canonical runner permits a full
fresh replay; the exact audit-only repair command is also documented.

Nonvacuity: explicit cut-level endpoints for the six-vertex one-edge graph,
balanced K2 and C5 (via its explicit doubled cut and descent) compile without
BCLEventual. Nonzero cost checks detect missing n^2 and directed-edge double
counting. Every three-vertex set of C5 has an edge, so the false ceil variant
is rejected. Empty, balanced, side-mass, scaling and qualified square
controls pass their intended tests. These are not sharpness claims.

All 654 files in the eleven prior builder freezes remain hash-identical.
The original E10 ambiguous-square result is preserved; its accepted critic
correction is bound here and the new filter excludes ambiguity/placeholders.
{len(fails)} failed development compilation(s) and the initial failed audit are retained.

This formalizes the existing written E5 route. It does not prove the .02 bound, the
external BCL theorem, novelty or best-known status. Independent acceptance
is pending. No further route or repository action was started by builder.
'''
 (H/'REPORT.txt').write_text(report)
 (H/'REPLAY-INSTRUCTIONS.txt').write_text('REPLAY\n\nFrom this packet, run python3 replay.py. It creates a fresh copied-source directory, rebuilds the exact34-module closure plus Audit, audits all public theorem axioms, checks every module using the separate leanchecker, and runs eight expected mathematical rejections. It uses only the existing Lean4.35/Mathlib pin. It does not install packages or import development products.\n\nThe completed builder run first rebuilt all 34 proof modules, then repaired the audit-name parser. Its exact continuation is:\n  python3 replay.py --resume-audit '+str(vp.parent.relative_to(H))+'\nThe option requires a recorded compile-Audit failure, successful fresh builds for every proof module and exact source-hash equality. It saves the previous Audit/log/verification, recompiles Audit, and runs the full audit, kernel and control stages. This is a repair of fresh evidence, not reuse of development products. A new reviewer should use the default full fresh run.\n\nprovenance.py checks all 654 prior frozen files and records exact source/pin bindings. Do not run finalization or provenance against an accepted frozen copy; use a copied review directory.\n')
 (H/'REMAINING.txt').write_text('REMAINING\n\nIndependent review and acceptance of this exact freeze. BCLEventual remains the explicit external theorem input; it has not been proved in this work. No mathematical integration obligation for the stated conditional .0251 endpoint is left as a hypothesis beyond that input and the triangle-free graph domain. No assertion is made about novelty, best-known constants or the .02 conjecture. Root owns any manuscript, state or repository integration.\n')
 (H/'FINAL-INDEX.json').write_text(json.dumps({'status':'frozen-for-independent-review','endpoint':'Erdos128.FinalGraph.sparse_half_251_10000','external_input':'Erdos128.CompletionBridge.BCLEventual','statement':'EXACT-STATEMENT.txt','proof_map':'PROOF-MAP.txt','closure':'complete-closure.json','evidence':str(vp.relative_to(H)),'evidence_sha256':sha(vp),'public_theorem_audits':len(v['declarations_audited']),'proof_modules':34,'kernel_modules':35,'negative_controls':len(v['negative_controls']),'prior_preserved_files':654,'development_failures':len(fails),'audit_parser_repair':v.get('audit_parser_repair')},indent=2)+'\n')
 files={}
 for p in sorted(H.rglob('*')):
  if not p.is_file() or p.name=='artifact-sha256.json' or '__pycache__' in p.parts or any(x in p.name for x in ['.olean','.ilean','.ir']):continue
  files[str(p.relative_to(H))]=sha(p)
 manifest={'frozen_utc':datetime.now(timezone.utc).isoformat(),'scope':'E11 actual all finite graph .0251 floor-half endpoint conditional only on transparent BCLEventual, full source closure and fresh proof evidence; pending independent acceptance','excluded':'Compiled Lean products and Python cache. Build product hashes are recorded in verification.json.','files':files}
 p=H/'artifact-sha256.json';p.write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'manifest':str(p),'sha256':sha(p),'files':len(files),'bytes':sum((H/x).stat().st_size for x in files),'verification':str(vp.relative_to(H)),'verification_sha256':sha(vp),'audits':len(v['declarations_audited']),'kernel_modules':35,'controls':len(v['negative_controls'])},indent=2))
if __name__=='__main__':main()
