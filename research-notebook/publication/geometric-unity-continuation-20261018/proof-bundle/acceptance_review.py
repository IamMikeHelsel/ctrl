#!/usr/bin/env python3
"""Independent outcome review of recorded replay plus the additive inventory gate."""
from pathlib import Path
import hashlib,json
from inventory_check import check_inventory,require
B=Path(__file__).resolve().parent
r=json.loads((B/'latest-integrated-result.json').read_text())
O=B/r['run']; C=B/'.replay'/O.name
spec=json.loads((B/'verification-inventory.json').read_text())
modules=set(spec['mathematical_modules']+spec['reviewer_modules'])
false={Path(p).name.removesuffix('.lean.txt') for p in spec['false_clients']}
require(r['status']=='PASS','Replay result is not PASS')
require((r['built_modules'],r['kernel_replays'],r['false_controls'])==(48,48,20),'Wrong replay counts')
steps={s['name']:s for s in r['steps']}
require(len(steps)==len(r['steps']),'Duplicate replay step')
expected={'build-'+m for m in modules}|{'kernel-'+m for m in modules}|false|{'FinalAudit'}
# Future hardened replays may add a final inventory subprocess; the reviewed
# historical replay has exactly the mathematical phases above.
require(set(steps) in (expected,expected|{'InventoryFinal'}),'Replay step inventory mismatch')
for label,step in steps.items():
 log=(O/(label+'.txt')).read_text()
 if label in false:
  require(step['returncode']!=0 and 'unsolved goals' in log,'False control did not fail mathematically: '+label)
  require(not any(w in log.lower() for w in ['unknown identifier','unknown module','type mismatch','unexpected token','failed to synthesize','file not found']),'Infrastructure false-control failure: '+label)
 else:require(step['returncode']==0,'Positive verification failed: '+label)
audit=(O/'FinalAudit.txt').read_text();rows=[s for s in audit.splitlines() if s.startswith('AUDIT|')]
counts={m:sum(s.startswith('AUDIT|'+m+'|') for s in rows) for m in modules}
require(set(r['audit_counts'])==modules and r['audit_counts']==counts,'Audit count mismatch')
require(all(counts.values()) and len(rows)==r['audited_declarations'],'Missing audited module or declaration count mismatch')
require(set(r['source_hashes'])==modules,'Wrong recorded source-hash set')
for m,h in r['source_hashes'].items():
 require(hashlib.sha256((C/(m+'.lean')).read_bytes()).hexdigest()==h,'Recorded copied source differs: '+m)
inventory=check_inventory(B,C,complete=True)
(O/'inventory-additive-after.json').write_text(json.dumps(inventory,indent=2)+'\n')
out={'status':'PASS','replay_log':str(O.relative_to(B)),'built_modules':48,'kernel_replays':48,'false_clients':20,'audited_declarations':len(rows),'inventory':inventory,'invoked_runner_sha256':hashlib.sha256((O/'invoked-runner.py').read_bytes()).hexdigest(),'current_runner_sha256':hashlib.sha256((B/'integrated_replay.py').read_bytes()).hexdigest(),'boundary':'Complete proof replay used invoked-runner.py. The later hardened harness was not rerun wholesale; its independent additive inventory/outcome gates validate all original replay inputs, copied controls, audit template and recorded outcomes.'}
(B/'acceptance-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
