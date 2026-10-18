#!/usr/bin/env python3
"""Run AFTER the copied main replay; no prior research products are imported."""
from pathlib import Path
import json,hashlib,os,subprocess,time,sys,re,shutil
P=Path(__file__).resolve().parent
work=Path(sys.argv[1]).resolve()
base=json.loads((work/'verification.json').read_text())
assert base['passed'] and base['source_hashes_stable']
binary=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
env=os.environ.copy();env['PATH']=str(binary)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=base['lean_path']
shutil.copyfile(P/'CriticControls.lean',work/'CriticControls.lean')
result={'base_verification':str(work/'verification.json'),'base_sha256':hashlib.sha256((work/'verification.json').read_bytes()).hexdigest(),'lean_path':env['LEAN_PATH'],'runs':[],'axioms':{},'passed':False}
def save(): (P/'extra-verification.json').write_text(json.dumps(result,indent=2)+'\n')
def run(name,args):
 start=time.monotonic()
 try:
  r=subprocess.run(args,cwd=work,env=env,capture_output=True,text=True,timeout=120);code=r.returncode;out=r.stdout+r.stderr
 except subprocess.TimeoutExpired as e: code=124;out=str(e.stdout)+'\n'+str(e.stderr)+'\nTIMEOUT\n'
 log=P/(name+'.log');log.write_text(out)
 result['runs'].append({'label':name,'command':args,'exit':code,'seconds':time.monotonic()-start,'log':log.name});save();print(name,code,flush=True)
 return code,out
code,out=run('compile-CriticControls',[str(binary/'lean'),'-o','CriticControls.olean','CriticControls.lean']);assert code==0
for name,axes in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out):result['axioms'][name]=[x.strip() for x in axes.split(',') if x.strip()]
assert len(result['axioms'])==2
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in result['axioms'].values())
code,_=run('kernel-CriticControls',[str(binary/'leanchecker'),'CriticControls','-v']);assert code==0
bad='''import CriticControls
open Erdos128 Erdos128.FiniteProfileControls
example : ∀ z : Fin 6 → ℚ, IsFractionalHalf z → normalizedEdgeCostQ oneEdge z ≤ 1 / 100 := by
  have h := Erdos128.E9CriticControls.not_every_half_has_endpoint_cost
  simp_all
'''
(work/'BadUniversalHalf.lean').write_text(bad);(P/'BadUniversalHalf.lean').write_text(bad)
code,out=run('reject-BadUniversalHalf',[str(binary/'lean'),'BadUniversalHalf.lean'])
assert code not in (0,124) and 'unsolved goals' in out
assert not re.search(r'Unknown identifier|unknown constant|unexpected token|failed to synthesize',out)
result['passed']=True
result['source_sha256']=hashlib.sha256((P/'CriticControls.lean').read_bytes()).hexdigest()
result['module_product_sha256']=hashlib.sha256((work/'CriticControls.olean').read_bytes()).hexdigest()
save()
