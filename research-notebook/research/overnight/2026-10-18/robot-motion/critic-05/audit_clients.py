from pathlib import Path
import json,os,subprocess
HERE=Path(__file__).resolve().parent
E=json.loads((HERE/'environment.json').read_text());F=Path(E['fresh_root'])
env=os.environ.copy();env.update({k:E[k] for k in ['ELAN_HOME','LEAN_PATH','PATH']})
mods=['ReviewClients']+['JSON'+p.stem.replace('-','_') for p in sorted((HERE.parent/'builder-05/clients').glob('*.json'))]
results=[]
for m in mods:
    assert (F/(m+'.olean')).exists(),m
    src=f'''import {m}
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if env.allImportedModuleNames[idx.toNat]! == `{m} then
        if info.isUnsafe then throwError "unsafe declaration {{n}}"
        if info.isAxiom then throwError "axiom declaration {{n}}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError "unapproved axiom {{ax}} in {{n}}"
        logInfo m!"DECL|{{n}}|{{used}}"
'''
    target=HERE/('Audit'+m+'.lean');target.write_text(src)
    r=subprocess.run([E['lean'],'--root='+str(F),str(target)],cwd=F,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (HERE/'logs'/('audit-'+m+'.log')).write_text(r.stdout)
    assert r.returncode==0,(m,r.stdout)
    results.append({'module':m,'declarations':r.stdout.count('DECL|'),'axiom_audit':'PASS','unsafe':False})
(HERE/'client-axiom-audit.json').write_text(json.dumps({'status':'PASS','modules':results,'total_local_client_declarations':sum(x['declarations'] for x in results)},indent=2)+'\n')
