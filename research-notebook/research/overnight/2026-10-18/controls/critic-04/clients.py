from pathlib import Path
import json,subprocess,os,time,hashlib,re
HERE=Path(__file__).resolve().parent
cfg=json.loads((HERE/'environment.json').read_text());env=os.environ.copy();env.update(cfg['env']);root=Path(cfg['build']);lean=cfg['lean'];steps=[]
(root/'ReviewClients.lean').write_bytes((HERE/'ReviewClients.lean').read_bytes())
def run(label,args,negative=False):
 p=HERE/'logs'/(label+'.log');start=time.monotonic()
 with p.open('w') as out: r=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600)
 s=p.read_text();ok=r.returncode!=0 if negative else r.returncode==0
 if negative:ok=ok and 'unsolved goals' in s and not any(x in s for x in ['unknown','failed to synthesize','maximum recursion','maximum heartbeats'])
 steps.append({'label':label,'exit':r.returncode,'passed':ok,'seconds':time.monotonic()-start,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 (HERE/'clients.json').write_text(json.dumps({'passed':False,'steps':steps},indent=2)+'\n');print(label,r.returncode,flush=True);assert ok,label
run('review-clients',[lean,'--root='+str(root),'-o',str(root/'ReviewClients.olean'),str(root/'ReviewClients.lean')])
run('kernel-review-clients',[cfg['checker'],'ReviewClients','-v'])
names=re.findall(r'^theorem (\w+)',(HERE/'ReviewClients.lean').read_text(),re.M)
p=root/'ClientAxioms.lean';p.write_text('import ReviewClients\n'+'\n'.join('#print axioms LeanControls.QuadraticIndependentReview.'+n for n in names)+'\n')
run('client-axioms',[lean,str(p)])
a=(HERE/'logs/client-axioms.log').read_text();entries=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",a)
assert len(entries)==len(names)
assert all(set(x.strip() for x in used.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for name,used in entries)
controls={
 'unbounded-disturbance':'energyRate 80 2 2 0 0 ≤ 20*(1-energy 2 0 0)',
 'outside-rate':'energyRate 160 (-1) (-2) 2 (-1) ≤ 20*(1-energy (-2) 2 (-1))',
 'initial-unit-reset':'energy 16 0 0 ≤ 1',
 'instant-terminal-speed':'|movingState 0 1| ≤ 1/1000',
 'wrong-inherited-endpoint':'movingState 0 = DirectReference.reference 7 (DirectReference.duration 7)',
 'zero-speed-after-two':'stepHold 2 1 = 0',
}
neg=HERE/'negative-controls';neg.mkdir(exist_ok=True)
for name,claim in controls.items():
 code='import ReviewClients\nopen LeanControls LeanControls.QuadraticHold LeanControls.QuadraticWitness LeanControls.QuadraticIndependentReview\nexample : '+claim+' := by\n  norm_num [energy,energyRate,movingState,stepHold,DirectReference.reference_endpoint]\n'
 p=neg/(name+'.lean');p.write_text(code);client=root/(name.replace('-','_')+'.lean');client.write_text(code);run('negative-'+name,[lean,str(client)],True)
(HERE/'clients.json').write_text(json.dumps({'passed':True,'positive_clients':len(names),'negative_clients':len(controls),'axioms':{name:used for name,used in entries},'steps':steps},indent=2)+'\n')
print('PASS',len(names),len(controls))
