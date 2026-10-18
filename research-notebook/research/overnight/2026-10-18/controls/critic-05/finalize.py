#!/usr/bin/env python3
"""Freeze only the completed review; preserve all recorded failed attempts."""
from pathlib import Path
import datetime,hashlib,json
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
replay=json.loads((HERE/'replay.json').read_text())
clients=json.loads((HERE/'clients.json').read_text())
exact=json.loads((HERE/'exact-review.json').read_text())
assert replay['passed'] and clients['passed'] and exact['passed']
assert len(replay['order'])==54 and replay['audited_declarations']==3184
assert len(replay['kernel_targets'])==11
assert clients['positive_theorems']==15 and clients['audited_client_declarations']==31
assert clients['new_false_clients']==8 and clients['inherited_false_clients']==6
assert all(s['passed'] for s in clients['steps'])
for rel,record in replay['input_manifests'].items():
    manifest=HERE.parents[1]/rel
    assert sha(manifest)==record['sha256']
    files=json.loads(manifest.read_text())['files']
    for name,entry in files.items():
        expected=entry if isinstance(entry,str) else entry['sha256']
        assert sha(manifest.parent/name)==expected,(rel,name)
for module,record in replay['closure'].items():
    assert sha(WORK/record['path'])==record['sha256']
    assert sha(HERE/'fresh'/(module.replace('.','/')+'.lean'))==record['sha256']
assert sha(HERE/'ReviewClients.lean')==sha(HERE/'fresh/ReviewClients.lean')==clients['positive_source_sha256']
assert 'error:' not in (HERE/'statement-types.log').read_text()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
result={'decision':'ACCEPT bounded scalar proof gate; no builder repair required',
 'frozen_at_utc':now,'builder_manifest_sha256':replay['input_manifests']['controls/builder-05/artifact-sha256.json']['sha256'],
 'fresh_builder_modules':54,'builder_local_declarations_audited':3184,
 'source_kernel_replays':11,'reviewer_theorems':15,'reviewer_declarations_audited':31,
 'reviewer_kernel_replays':1,'new_false_clients':8,'inherited_false_clients':6,
 'exact_witness_anchors':len(exact['anchor_rows']),
 'exact_cell_boundary_jet_equalities':len(exact['cell_boundary_jet_equalities']),
 'preserved_input_manifest_count':len(replay['input_manifests']),
 'preserved_input_file_entries':sum(x['files'] for x in replay['input_manifests'].values()),
 'next':'Stop new controls branches; integrate this exact scope and perform publication/artifact review.',
 'limits':'One supplied classical scalar trajectory. Global terminal time 3.42s, residual bands, no exact rest, no hardware/implementation/novelty claim.'}
(HERE/'review-result.json').write_text(json.dumps(result,indent=2)+'\n')
target=HERE/'artifact-sha256.json';assert not target.exists()
files={}
for path in sorted(HERE.rglob('*')):
    if not path.is_file() or path==target:continue
    rel=path.relative_to(HERE)
    if '__pycache__' in rel.parts:continue
    if rel.parts[0]=='fresh' and path.suffix!='.lean':continue
    files[str(rel)]={'sha256':sha(path),'bytes':path.stat().st_size}
target.write_text(json.dumps({'frozen_at_utc':now,'status':'independently accepted bounded scalar gate','files':files},indent=2)+'\n')
assert all(sha(HERE/p)==r['sha256'] for p,r in files.items())
print(json.dumps({'manifest_sha256':sha(target),'files':len(files),'decision':result['decision']}))
