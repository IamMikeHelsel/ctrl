"""Validate preservation and exact translations; this does not run Lean."""
from pathlib import Path
from fractions import Fraction as F
import datetime,hashlib,json,tarfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
bindings={}
def bind(p,expected=None):
 actual=sha(p)
 if expected is not None:assert actual==expected,str(p)
 bindings[p.relative_to(ROOT).as_posix()]=actual
 return actual

v=read(ROOT/'publication/robust-manuscript/verification.json')
bind(ROOT/'publication/robust-manuscript/verification.json')
bind(ROOT/'publication/robust-manuscript/main.tex',v['tex_sha256'])
bind(ROOT/'publication/robust-manuscript/main.pdf',v['pdf_sha256'])
bind(ROOT/'publication/robust-manuscript/review.txt',v['semantic_review_sha256'])
replay_path=ROOT/'publication/robust-final-fresh-replay.json'
bind(replay_path,v['source_replay_manifest_sha256'])
replay=read(replay_path)
assert replay['status']=='passed' and replay['expected_project_modules']==63
assert replay['public_declarations_audited']==830 and not replay['unexpected_axioms']
whole_path=ROOT/'publication/robust-project-verification.json'
bind(whole_path,v['whole_project_manifest_sha256'])
whole=read(whole_path)
assert whole['status']=='verified' and len(whole['steps'])==5
for name,expected in replay['original_source_sha256_before'].items():
 bind(ROOT/'lean-controls'/name,expected)
for entry in replay['durable_artifacts'].values():bind(ROOT/'publication'/Path(entry['path']).name,entry['sha256'])
archive=ROOT/'publication/robust-final-fresh-replay.sources.tar.gz'
with tarfile.open(archive) as t:
 members={x.name:x for x in t.getmembers() if x.isfile()}
 assert len(members)==105
 for name,expected in replay['original_source_sha256_before'].items():
  assert hashlib.sha256(t.extractfile(members['lean-controls/'+name]).read()).hexdigest()==expected

frozen=[
 ('research/overnight/2026-10-18/controls/builder-05/artifact-sha256.json','4036417f36ccf705244f9b285c8bdf4e98245d325c522a280ed8aeeed9ab2f00'),
 ('research/overnight/2026-10-18/controls/critic-05/artifact-sha256.json','3fbe0730f46abcec1025548b3b254f4618554004a014962c10d32dd0773bac56'),
 ('publication/robot-motion/overnight-reviewer-bundle-v4/artifact-sha256.json','73f004177733a1384a2bb7f22417d910c9da6b359088159c8d58f46ab13b23ed')]
counts={}
for name,expected in frozen:
 p=ROOT/name;bind(p,expected);d=read(p);d=d.get('files',d);counts[name]=len(d)
 for rel,item in d.items():bind(p.parent/rel,item['sha256'] if isinstance(item,dict) else item)

# Independent exact arithmetic for the printed scale and ablations.
tau0=F(1,10);U=F(2);assert 2*U*tau0*tau0==F(1,25)
assert tau0/5==F(1,50) and U/100==F(1,50)
assert tau0/F(11,10)==F(1,11) and tau0/F(9,10)==F(1,9)
P=[[F(38,5),F(257,25),F(5)],[F(257,25),F(1319,50),F(769,50)],[F(5),F(769,50),F(278,25)]]
energy=lambda z:sum(z[i]*P[i][j]*z[j] for i in range(3) for j in range(3))
assert energy([0,0,1])<12
assert energy([F(19,10),1,0])>12
eta=F(15,902);H=F(1,5);W=F(1,100)
assert F(16)*(H+1/eta)*W*W==F(181,1875)<12*eta
assert F(27511,500)*(H+1/eta)*W*W==F(4979491,15000000)>12*eta
assert F(71,50)+2==F(171,50)

report={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'passed':True,'mode':'preservation and exact arithmetic checks; no new Lean replay',
 'primary_source_files_verified':105,'primary_archive_files_verified':105,
 'primary_historical_replay_modules':63,'primary_historical_public_declarations':830,
 'primary_historical_project_steps':5,'companion_frozen_manifest_entries':counts,
 'bound_input_files':len(bindings),'exact_physical_translation_passed':True,
 'exact_initial_set_and_budget_checks_passed':True,'new_theorems':0,
 'hardware_validation':False,'novelty_established':False,
 'trust_note':'Existing frozen proof records are verified by hash. This run checks neither proof-system bootstrapping nor publication novelty.'}
(HERE/'input-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
