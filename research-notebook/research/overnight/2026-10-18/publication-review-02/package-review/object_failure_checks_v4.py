from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parent; P=R/'package-v4';F=R/'fresh-replay-v4';C=R/'client-tests-v4';results=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def check(name,expected):
 out=C/name;cmd=['python3',str(P/'client.py'),'--input',str(P/'examples/on-time.json'),'--replay-output',str(F),'--output',str(out)]
 got=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=650);(C/(name+'.log')).write_text(got.stdout)
 assert got.returncode!=0 and expected in got.stdout and not (out/'result.json').exists(),got.stdout
 results.append({'name':name,'passed':True,'exit_code':got.returncode,'expected_error':expected,'command':cmd}); print(name,'PASS',flush=True)
obj=F/'.build/FutureCommit.olean';original=obj.read_bytes()
try:
 obj.write_bytes(original+b'reviewer deliberate changed object')
 changed_hash=sha(obj.read_bytes());check('changed-replay-object','Changed replay objects')
finally:obj.write_bytes(original)
assert sha(obj.read_bytes())==sha(original)
try:
 obj.rename(obj.with_suffix('.reviewer-held'))
 check('missing-replay-object','Changed replay objects')
finally:obj.with_suffix('.reviewer-held').rename(obj)
metadata=F/'results.json';record=metadata.read_bytes()
try:
 v=json.loads(record);v['passed']=False;metadata.write_text(json.dumps(v));check('incomplete-replay','Replay did not pass')
 v=json.loads(record);v.pop('compiled_objects');metadata.write_text(json.dumps(v));check('missing-object-record','compiled_objects')
finally:metadata.write_bytes(record)
assert metadata.read_bytes()==record and obj.read_bytes()==original
for mode,error in [('kernel-nonzero','kernel failed'),('missing-axiom-audit','Missing generated-theorem axiom audit')]:
 cmd=['python3',str(R/'client_failure_injection_v4.py'),mode];got=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=650);(C/('injected-'+mode+'.log')).write_text(got.stdout)
 assert got.returncode!=0 and error in got.stdout and not (C/('injected-'+mode)/'result.json').exists(),got.stdout
 results.append({'name':'injected-'+mode,'passed':True,'exit_code':got.returncode,'expected_error':error,'command':cmd,'scope':'Reviewer-injected execution failure, not a mathematical negative client.'});print(mode,'PASS',flush=True)
(R/'object-failure-results-v4.json').write_text(json.dumps({'tests':results,'original_object_sha256':sha(original),'changed_object_sha256':changed_hash,'restored_object_sha256':sha(obj.read_bytes()),'original_record_sha256':sha(record),'restored_record_sha256':sha(metadata.read_bytes())},indent=2)+'\n')
