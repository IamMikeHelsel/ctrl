from pathlib import Path
import hashlib,json,subprocess,time
R=Path(__file__).resolve().parent;P=R/'package-v3';F=R/'fresh-replay-v3';r=R/'output-snapshot-race-v3';r.mkdir();inp=P/'examples/on-time.json';before=inp.read_bytes();value=json.loads(before);value['liveTask']['goal']='1/200';after=(json.dumps(value,indent=2)+'\n').encode();(r/'before.json').write_bytes(before);(r/'after.json').write_bytes(after);out=r/'output'
cmd=['python3',str(P/'client.py'),'--input',str(inp),'--replay-output',str(F),'--output',str(out)];start=time.monotonic()
with (r/'console.log').open('w') as stream:
 proc=subprocess.Popen(cmd,text=True,stdout=stream,stderr=subprocess.STDOUT)
 while not (out/'ClientProbe.lean').exists() and proc.poll() is None and time.monotonic()-start<120:time.sleep(.005)
 assert (out/'ClientProbe.lean').exists()
 (out/'input.json').write_bytes(after)
 changed=time.monotonic()-start;code=proc.wait(timeout=650)
assert code==0,(r/'console.log').read_text()
res=json.loads((out/'result.json').read_text());assert res['decision'] is True
assert 'def t : Task := ⟨(0/1:ℚ)' in (out/'ClientProof.lean').read_text()
oldhash=hashlib.sha256(before).hexdigest();newhash=hashlib.sha256(after).hexdigest()
assert res['input_sha256']==newhash!=oldhash
finding={'scope':'Controlled concurrent edit inside newly created output folder. Distinct from the external input-path race and stronger than ordinary exclusive output ownership.','proved_input_sha256':oldhash,'recorded_input_sha256':res['input_sha256'],'saved_snapshot_sha256':newhash,'result_mislabels_proved_input':True,'raw_external_input_unchanged':inp.read_bytes()==before,'proof_literals_match_original':True,'proof_compiled_and_kernel_passed':True,'edit_seconds_after_start':changed,'command':cmd,'suggested_repair':'Set result.input_sha256 from hashlib.sha256(raw).hexdigest(); require saved input snapshot bytes still equal raw before success.'}
(r/'finding.json').write_text(json.dumps(finding,indent=2)+'\n');print(json.dumps(finding,indent=2))
