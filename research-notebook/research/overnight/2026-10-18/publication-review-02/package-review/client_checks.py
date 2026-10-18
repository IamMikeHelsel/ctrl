from pathlib import Path
import copy,hashlib,json,subprocess,time,shutil
R=Path(__file__).resolve().parent; P=R/'package-v3'; F=R/'fresh-replay-v3'; C=R/'client-tests'; C.mkdir(exist_ok=True)
summary=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def command(inp,out,replay=F):return ['python3',str(P/'client.py'),'--input',str(inp),'--replay-output',str(replay),'--output',str(out)]
def run(name,inp,decision=None,error=None,replay=F):
 out=C/name
 cmd=command(inp,out,replay)
 p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=650)
 (C/(name+'.console.log')).write_text(p.stdout)
 got=json.loads((out/'result.json').read_text()) if (out/'result.json').exists() else None
 if error:
  assert p.returncode!=0 and got is None and error in p.stdout,(name,p.returncode,p.stdout)
 else:
  assert p.returncode==0 and got['compiled_proof'] and got['kernel_replay'] and got['decision']==decision,(name,p.returncode,p.stdout)
  assert got['input_sha256']==sha(out/'input.json')==sha(inp)
 summary.append({'name':name,'exit_code':p.returncode,'result':got,'expected_error':error,'command':cmd,'passed':True});print(name,'PASS',flush=True)
 (R/'client-results.json').write_text(json.dumps(summary,indent=2)+'\n')
for inp in sorted((P/'examples').glob('*.json')):run('example-'+inp.stem,inp,inp.stem=='on-time')
original=json.loads((P/'examples/on-time.json').read_text())
bad=[]
def case(name,change,error):
 v=copy.deepcopy(original);change(v);bad.append((name,json.dumps(v),error))
case('rational-number',lambda v:v['liveTask'].__setitem__('goal',0),'rationals must')
case('rational-decimal',lambda v:v['liveTask'].__setitem__('goal','0.5'),'rationals must')
case('rational-zero-denominator',lambda v:v['liveTask'].__setitem__('goal','1/0'),'ZeroDivisionError')
case('rational-negative-denominator',lambda v:v['liveTask'].__setitem__('goal','1/-2'),'rationals must')
case('rational-injection',lambda v:v['liveTask'].__setitem__('goal','0); axiom escape : False'),'rationals must')
case('rational-bool',lambda v:v['liveTask'].__setitem__('goal',True),'rationals must')
case('rational-too-long',lambda v:v['liveTask'].__setitem__('goal','1'*129),'rationals must')
case('version-bool',lambda v:v['liveBase'].__setitem__('version',True),'version must')
case('version-negative',lambda v:v['liveBase'].__setitem__('version',-1),'version must')
case('version-float',lambda v:v['liveBase'].__setitem__('version',7.0),'version must')
case('version-string',lambda v:v['liveBase'].__setitem__('version','7'),'version must')
case('missing-field',lambda v:v['timing'].pop('dispatch'),'wrong fields')
case('extra-field',lambda v:v['timing'].__setitem__('spare','0'),'wrong fields')
case('events-object',lambda v:v['liveBase'].__setitem__('events',{}),'events must')
case('bad-event-length',lambda v:v['liveBase'].__setitem__('events',[['0']]),'event has time')
case('candidates-object',lambda v:v['pending'].__setitem__('candidates',{}),'candidates must')
bad += [('duplicate-top',json.dumps(original)[:-1]+',"timing":'+json.dumps(original['timing'])+'}', 'Duplicate JSON key'),('duplicate-nested',json.dumps(original).replace('"goal": "0"','"goal": "0", "goal": "1/200"',1),'Duplicate JSON key'),('too-large',' '*1_000_001,'Input exceeds prototype file limit')]
inputs=C/'bad-inputs';inputs.mkdir()
for name,raw,error in bad:
 inp=inputs/(name+'.json');inp.write_text(raw);run('parser-'+name,inp,error=error)
# Check equal boundary and normalized rational strings with real proofs.
for name,change,decision in [('equal-clock-boundary',lambda v:v.__setitem__('timing',{'completion':'31/50','commitTime':'31/50','dispatch':'0'}),True),('negative-dispatch',lambda v:v['timing'].__setitem__('dispatch','-1/100'),False),('rational-normalization',lambda v:(v['liveTask'].__setitem__('goal','-0'),v['liveBase'].__setitem__('width','002/010')),True)]:
 v=copy.deepcopy(original);change(v);inp=C/(name+'.json');inp.write_text(json.dumps(v));run(name,inp,decision)
# Replace the original input path after the probe is visible. The saved snapshot
# and generated literals must still match the originally read goal-zero request.
race=C/'input-path-race';race.mkdir();inp=race/'mutable-input.json';before=(P/'examples/on-time.json').read_bytes();inp.write_bytes(before)
after=copy.deepcopy(original);after['liveTask']['goal']='1/200';afterbytes=(json.dumps(after,indent=2)+'\n').encode();(race/'before.json').write_bytes(before);(race/'after.json').write_bytes(afterbytes)
out=race/'output';cmd=command(inp,out);start=time.monotonic()
with (race/'console.log').open('w') as stream:
 p=subprocess.Popen(cmd,stdout=stream,stderr=subprocess.STDOUT,text=True)
 while not (out/'ClientProbe.lean').exists() and p.poll() is None and time.monotonic()-start<120:time.sleep(.005)
 assert (out/'ClientProbe.lean').exists(),'No probe observed'
 inp.write_bytes(afterbytes);changed=time.monotonic()-start
 code=p.wait(timeout=650)
assert code==0,(race/'console.log').read_text()
res=json.loads((out/'result.json').read_text());assert res['decision'] is True
assert (out/'input.json').read_bytes()==before
assert res['input_sha256']==hashlib.sha256(before).hexdigest()!=sha(inp)
assert 'def t : Task := ⟨(0/1:ℚ)' in (out/'ClientProof.lean').read_text()
finding={'passed':True,'input_path_changed_after_probe_seconds':changed,'original_sha256':hashlib.sha256(before).hexdigest(),'changed_path_sha256':sha(inp),'saved_snapshot_sha256':sha(out/'input.json'),'result':res,'command':cmd}
(race/'finding.json').write_text(json.dumps(finding,indent=2)+'\n');summary.append({'name':'input-path-race','passed':True,'evidence':str(race/'finding.json')})
(R/'client-results.json').write_text(json.dumps(summary,indent=2)+'\n');print('input-path-race PASS',flush=True)
