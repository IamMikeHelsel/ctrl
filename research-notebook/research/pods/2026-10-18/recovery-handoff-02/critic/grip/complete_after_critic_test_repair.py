#!/usr/bin/env python3
"""Recorded one-time critic harness repair. Canonical fresh replay uses ../replay_grip.py.
Preserve the initial failed critic-only arithmetic test. All proof source builds,
axiom audits, and module kernels already passed and remain recorded unchanged.
"""
from pathlib import Path
import json,hashlib,os,re,shutil,subprocess,time,ast
OUT=Path(__file__).resolve().parent;HERE=OUT.parent;WORK=HERE.parents[4];BASE=WORK/'lean-controls';B=HERE.parent/'grip-builder';FRESH=OUT/'fresh';LOG=OUT/'logs'
script=HERE/'replay_grip.py';original=script.read_text();attempt=OUT/'critic-test-initial-attempt';attempt.mkdir(exist_ok=True)
for src in [script,OUT/'replay-results.json',LOG/'critic-semantic-checks.log',FRESH/'CriticRecoveryChecks.lean']:
 shutil.copy2(src,attempt/src.name)
old='example : Witness.state 3 1 = -Real.exp (-2) := by\n norm_num [Witness.state,LeanControls.UncertainLag.heldSolution]\n'
assert original.count(old)==1
script.write_text(original.replace(old,old+' ring\n'))
report=json.loads((OUT/'replay-results.json').read_text())
assert report['steps'][-1]['label']=='critic-semantic-checks' and not report['steps'][-1]['passed']
failed=report['steps'].pop();report['harness_attempts']=[{'status':'critic test tactic repaired; no builder source change','detail':'Added ring after norm_num left the exact identity -1+(1-exp(-2))=-exp(-2).','failed_step':failed,'preserved_directory':'critic-test-initial-attempt'}]
lean=Path(report['steps'][0]['command'][0]);checker=lean.with_name('leanchecker');env=os.environ.copy();env['LEAN_PATH']=report['lean_path'];env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
EXPECTED=report['builder_manifest_sha256'];mods=['ComparisonEnvelope','FirstStop','StoppingCertificate','ActualStop','Recovery','RecoveryWitness'];sources={n:(B if n.startswith('Recovery') else B/'inputs')/(n+'.lean') for n in mods}
core={n:BASE/Path(n.replace('.','/')+'.lean') for n in report['core_source_sha256']};names=list(report['axioms']);bv=json.loads((B/'verification.json').read_text())
# Reuse only the same runner, hash checks and final critic tail from the corrected
# canonical script. No source-build, axiom or kernel result is invented here.
code=script.read_text();tree=ast.parse(code)
for n in tree.body:
 if isinstance(n,ast.FunctionDef) and n.name in ['sha','frozen','save','run']:
  exec(compile(ast.Module(body=[n],type_ignores=[]),str(script),'exec'),globals())
assert frozen()
for n,p in sources.items():assert sha(p)==report['source_sha256'][n] and sha(FRESH/(n+'.lean'))==sha(p)
for n,p in core.items():assert sha(p)==report['core_source_sha256'][n] and sha(FRESH/Path(n.replace('.','/')+'.lean'))==sha(p)
repair_meta={'scope':'Critic-owned test tactic repair only. Canonical fresh replay is replay_grip.py followed by replay_grip_extra.py. This one-time completion script is historical evidence, not needed for clean replay.','before_script_sha256':sha(attempt/'replay_grip.py'),'after_script_sha256':sha(script),'preserved_files':{p.name:sha(p) for p in attempt.iterdir() if p.is_file()},'completion_script_sha256':sha(Path(__file__))}
(OUT/'critic-test-repair.json').write_text(json.dumps(repair_meta,indent=2)+'\n')
__file__=str(script)
tail=code[code.index("(FRESH/'CriticRecoveryChecks.lean').write_text"):]
exec(compile(tail,str(script),'exec'),globals())
