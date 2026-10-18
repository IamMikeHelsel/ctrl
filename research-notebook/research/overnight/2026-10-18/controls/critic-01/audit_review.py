#!/usr/bin/env python3
"""Audit the additional review witnesses after the fresh closure build."""
from pathlib import Path
import hashlib,json,os,re,subprocess
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
lake=str(WORK/'.tools/elan/bin/lake')
lean=subprocess.check_output([lake,'env','which','lean'],cwd=BASE,env=env,text=True).strip()
base_report=json.loads((HERE/'verification.json').read_text())
env['LEAN_PATH']=base_report['lean_path']
env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
source=HERE/'ReviewWitnesses.lean'
names=['LeanControls.SettlingIndependentReview.'+n for n in re.findall(r'^theorem\s+(\S+)',source.read_text(),re.M)]
p=HERE/'build/ReviewAudit.lean';p.write_text('import ReviewWitnesses\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
log=HERE/'logs/reviewer-axioms.log'
with log.open('w') as out:
    result=subprocess.run([lean,str(p)],cwd=HERE/'build',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=240)
assert result.returncode==0
axioms={n:[x.strip() for x in raw.split(',') if x.strip()] for n,raw in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log.read_text())}
assert set(axioms)==set(names)
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
report={'passed':True,'public_review_theorem_count':len(names),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'axioms':axioms,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
(HERE/'reviewer-axioms.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'review_theorems':len(names)}))
