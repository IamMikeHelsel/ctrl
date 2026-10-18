#!/usr/bin/env python3
"""Adversarial inventory tests use only throwaway copies; no Lean replay."""
from pathlib import Path
import json,re,shutil,subprocess,sys,tempfile
B=Path(__file__).resolve().parent.parent/'proof-bundle'
checker=B/'inventory_check.py'
spec=json.loads((B/'verification-inventory.json').read_text())
rows=[]
with tempfile.TemporaryDirectory(prefix='gu-inventory-review-') as scratch:
 root=Path(scratch)
 def fresh(name):
  target=root/name;target.mkdir()
  for relative in list(spec['files'])+list(spec['provenance_hashes'])+['verification-inventory.json']:
   p=target/relative;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(B/relative,p)
  return target
 def run(name,mutate=None,optimized=False,expected_pass=False):
  target=fresh(name)
  if mutate:mutate(target)
  cmd=[sys.executable]+(['-O'] if optimized else [])+[str(checker),'--bundle',str(target)]
  p=subprocess.run(cmd,text=True,capture_output=True);body=json.loads(p.stdout)
  passed=p.returncode==0
  if passed!=expected_pass:raise RuntimeError(name+' unexpected result '+p.stdout+p.stderr)
  if not expected_pass and body.get('status')!='FAIL':raise RuntimeError('Missing explicit failure')
  rows.append({'test':name,'expected_pass':expected_pass,'returncode':p.returncode,'result':body})
 run('pristine_copy_without_original_workspace',expected_pass=True)
 run('delete_baseline_module',lambda p:(p/'source/CliffordModel.lean').unlink())
 run('delete_baseline_false_control',lambda p:(p/'controls/FalseHalfCount.lean.txt').unlink())
 run('modify_baseline_control',lambda p:(p/'controls/CounterWitnesses.lean').write_bytes((p/'controls/CounterWitnesses.lean').read_bytes()+b'\n-- mutation\n'))
 run('add_unpinned_source',lambda p:(p/'accepted/Unpinned.lean').write_text('example : True := True.intro\n'))
 run('modify_audit_template',lambda p:(p/'controls/FinalAudit.lean').write_text('import CounterWitnesses\n'))
 run('optimized_missing_control',lambda p:(p/'controls/FalseHalfCount.lean.txt').unlink(),optimized=True)
 run('optimized_pristine_copy',optimized=True,expected_pass=True)
 def complete_run_test(name,mutate=None,expected_pass=False):
  target=fresh(name); run_dir=root/(name+'-run');run_dir.mkdir()
  positives=spec['mathematical_modules']+spec['reviewer_modules']
  for relative in spec['files']:
   f=Path(relative)
   if f.suffix=='.lean' and f.stem in positives:
    shutil.copy2(target/relative,run_dir/f.name)
   elif relative in spec['false_clients']:
    shutil.copy2(target/relative,run_dir/f.name.removesuffix('.txt'))
  template=(target/'controls/FinalAudit.lean').read_text()
  generated=template.replace('import CounterWitnesses','\n'.join('import '+m for m in positives))
  generated=re.sub(r'let owned : Array Name := #\[[^\]]*\]',
    'let owned : Array Name := #['+', '.join('`'+m for m in positives)+']',generated)
  (run_dir/'FinalAudit.lean').write_text(generated)
  if mutate:mutate(run_dir)
  p=subprocess.run([sys.executable,str(checker),'--bundle',str(target),'--run',str(run_dir),'--complete'],text=True,capture_output=True)
  body=json.loads(p.stdout)
  if (p.returncode==0)!=expected_pass:raise RuntimeError(name+' unexpected '+p.stdout+p.stderr)
  rows.append({'test':name,'expected_pass':expected_pass,'returncode':p.returncode,'result':body})
 complete_run_test('complete_copied_inputs',expected_pass=True)
 complete_run_test('alter_copied_positive',lambda p:(p/'CliffordModel.lean').write_bytes((p/'CliffordModel.lean').read_bytes()+b'\n-- copied mutation\n'))
 complete_run_test('delete_copied_false',lambda p:(p/'FalseHalfCount.lean').unlink())
 complete_run_test('reduce_generated_audit_coverage',lambda p:(p/'FinalAudit.lean').write_text((p/'FinalAudit.lean').read_text().replace('`CliffordModel, ','')))
result={'status':'PASS','tests':rows,'boundary':'File-inventory tests only. No Lean execution; temporary copied inputs deleted after run. Optimized Python remains checked because implementation uses explicit exceptions.'}
Path(__file__).with_name('inventory-mutation-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','tests':len(rows),'expected_rejections':sum(not r['expected_pass'] for r in rows)},indent=2))
