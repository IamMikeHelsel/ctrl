#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROBOT=HERE.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
expected={
 'certificate-03/builder':'740ebc266891b3f98b9ee567d19cced3c3ff187cbc091c08edfa52b276cd90fa',
 'latency-noise-05/builder':'8266eb7bd4da50d20f8fce651100126df1c9876b223c94a28d67c610fa3f4f78',
 'latency-noise-05/grader':'3c1c1d16f17e40ba92e9f240031040ea03dc45dda1a881cc03f3ff62d8fde45d',
 'native-execution-06/builder':'aaae586029babf2e9381d09ff34fb7b488495630c48abde27ab9b4d8ece1a803',
 'native-execution-06/grader':'abfb2e4527200fafafe6e93b57415920240796dc7497bc8e95c95ac25b4084bf',
 'rounded-handoff-07/builder':'75610f91ea3d0da654e87a21e3b0369c0c8bf6e8340d79b027951de96f0b444b',
 'rounded-handoff-07/grader':'df6e5b52f528875b6bbc2fd6d3a12a0dbeee6107bd7a7cc8898b994c843ed4af',
 'task-contract-08/builder':'c689b30ed18c9e6112ae3c243425d887d9abd1da77e01d3840e332409bd655a2',
 'moving-goal-08/builder':'ceac778c4d6775410e57b0f740e9e30ceeec36bccd0f1d86fbe01540c64db4e0'}
results=[]
for name in list(expected)+['intent-contract-07/analyst','rounded-handoff-07/bindings']:
 folder=ROBOT/name;m=folder/'artifact-sha256.json';hash=sha(m)
 if name in expected:assert hash==expected[name],name
 data=json.loads(m.read_text());files=data.get('files',data)
 for p,entry in files.items():
  wanted=entry['sha256'] if isinstance(entry,dict) else entry
  assert sha(folder/p)==wanted,(name,p)
 results.append({'directory':name,'manifest_sha256':hash,'files_verified':len(files)})
freeze=ROBOT/'task-contract-08/builder/source-freeze.json'
assert sha(freeze)=='b0d3d169e7fd53384cebad36af2f7682fa269ac9b59810375f56017e847d4c8a'
for p,entry in json.loads(freeze.read_text())['files'].items():assert sha(freeze.parent/p)==entry['sha256']
out={'passed':True,'frozen_artifacts':results,'all_older_frozen_artifacts_unchanged':True,'task08_source_freeze_sha256':sha(freeze)}
(HERE/'preservation-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
