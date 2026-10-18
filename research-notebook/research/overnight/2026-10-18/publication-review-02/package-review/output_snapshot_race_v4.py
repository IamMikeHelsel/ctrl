from pathlib import Path
import hashlib,json,subprocess,time
R=Path(__file__).resolve().parent;P=R/'package-v4';F=R/'fresh-replay-v4';r=R/'output-snapshot-race-v4';r.mkdir();inp=P/'examples/on-time.json';before=inp.read_bytes();value=json.loads(before);value['liveTask']['goal']='1/200';after=(json.dumps(value,indent=2)+'\n').encode();(r/'before.json').write_bytes(before);(r/'after.json').write_bytes(after);out=r/'output'
cmd=['python3',str(P/'client.py'),'--input',str(inp),'--replay-output',str(F),'--output',str(out)];start=time.monotonic()
with (r/'console.log').open('w') as stream:
 proc=subprocess.Popen(cmd,text=True,stdout=stream,stderr=subprocess.STDOUT)
 while not (out/'ClientProbe.lean').exists() and proc.poll() is None and time.monotonic()-start<120:time.sleep(.005)
 assert (out/'ClientProbe.lean').exists()
 (out/'input.json').write_bytes(after);changed=time.monotonic()-start;code=proc.wait(timeout=650)
log=(r/'console.log').read_text()
assert code!=0 and 'Input snapshot changed during proof' in log,log
assert not (out/'result.json').exists()
assert 'def t : Task := ⟨(0/1:ℚ)' in (out/'ClientProof.lean').read_text()
assert (out/'proof.log').exists() and (out/'kernel.log').exists()
finding={'passed':True,'scope':'Same concurrent saved-snapshot edit as the V3 counterexample; V4 must fail before success record.','exit_code':code,'raw_input_sha256':hashlib.sha256(before).hexdigest(),'changed_snapshot_sha256':hashlib.sha256(after).hexdigest(),'no_success_result':True,'proof_literals_match_original':True,'external_input_unchanged':inp.read_bytes()==before,'edit_seconds_after_start':changed,'command':cmd}
(r/'finding.json').write_text(json.dumps(finding,indent=2)+'\n');print(json.dumps(finding,indent=2))
