"""Bind accepted scratch evidence; does not claim unassembled trajectory theorem."""
import datetime, hashlib, json, re
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
replay=json.loads((OUT/'vertex-replay.json').read_text())
checks=[]
for rec in replay['results']:
 p=OUT/rec['file'];name=p.stem
 witness=json.loads(p.with_suffix('.certificate.json').read_text());data=json.loads(p.with_suffix('.input.json').read_text())
 suffix=f'\n#print axioms LeanControls.Generated.{name}.certified_decrease\n'
 source=p.read_text();assert source.endswith(suffix)
 checks.append({'name':name,'replay_hash_matches':sha(p)==rec['source_sha256'],
  'producer_source_hash_matches':hashlib.sha256(source[:-len(suffix)].encode()).hexdigest()==witness['generated_lean_sha256'],
  'input_hash_matches':hashlib.sha256(json.dumps(data,sort_keys=True).encode()).hexdigest()==witness['source_sha256']})
assert all(all(x for k,x in c.items() if k!='name') for c in checks)
log=(OUT/'RateEnclosure.log').read_text()
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
unexpected=sorted({a.strip() for _,xs in axioms for a in xs.replace('\n','').split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'})
assert len(axioms)==12 and not unexpected and 'error:' not in log
frozen=json.loads((BASE/'publication/application-fresh-replay.json').read_text())
changes=[]
for path,expected in frozen['original_source_sha256_after'].items():
 p=BASE/'lean-controls'/path
 if not p.exists() or sha(p)!=expected:changes.append(path)
source=(OUT/'RateEnclosure.lean').read_text()
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
manifest={'status':'PASS:12 generated vertex decrease closures and12 scratch analytic/arithmetic closures; NOT full uncertainty travel proof',
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'helper_compile_exit':0,'helper_compile_exit_basis':'observed final lake env lean command exit0 before manifest construction',
 'helper_audit_names':[name for name,_ in axioms], 'helper_unexpected_axioms':unexpected,
 'vertex_replay_all_pass':replay['all_pass'],'vertex_binding_checks':checks,
 'frozen_project_snapshot_id':frozen['snapshot_id_sha256'],
 'frozen_project_files_compared':len(frozen['original_source_sha256_after']),
 'frozen_project_files_changed':changes,
 'dependency_mode':'existing pinned Lean/mathlib and main-project cached imports; not independent bootstrap',
 'unfinished':['12 concrete model-to-generated-matrix identities and finite convex-energy composition',
 'Lean response-energy16 proof from prepared tensor coefficients',
 'uncertain actual sampled recurrence, global execution, continuity and physical scaling'],
 'artifact_hashes':{str(p.relative_to(OUT)):sha(p) for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='final-verification.json'},
 'assessment_sha256':sha(OUT.parent/'controls-assessment.txt')}
(OUT/'final-verification.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in manifest.items() if k not in ['artifact_hashes','vertex_binding_checks']},indent=2))
