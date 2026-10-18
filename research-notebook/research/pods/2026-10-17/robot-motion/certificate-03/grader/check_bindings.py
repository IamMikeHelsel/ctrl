"""Bind the literal Lean fixtures to the frozen inputs without the builder generator."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import re,json,hashlib
HERE=Path(__file__).resolve().parent;BUILDER=HERE.parent/'builder';POD=HERE.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse_es(s):return [(Q(a),Q(d)) for a,d in re.findall(r'\(([-0-9/]+),([-0-9/]+)\)',s)]
def jerk(h,es,t):return sum(d/h**3*sum((-1)**i*comb(4,i)*max((t-a)/h-i,Q(0)) for i in range(5)) for a,d in es)
def peak(h,es,c):return max(abs(jerk(h,es,t)) for t in {c}|{a+i*h for a,d in es for i in range(5) if a+i*h>=c})
text=(BUILDER/'Fixtures.lean').read_text()
defs={name:parse_es(es) for name,es in re.findall(r'^def frozen_(\w+) : List QEvent := (\[.*\])$',text,re.M)}
evals={name:(Q(c),parse_es(es),b=='true') for name,c,es,b in re.findall(r'^#eval \("([^"]+_admission_\d+)", check \(1/5\) \(15/2\) \(([^)]+)\) (\[.*\]), (true|false)\)$',text,re.M)}
checks=json.loads((POD/'lead-01/reference-checks.json').read_text())
assert len(defs)==7 and len(evals)==52
finals=[];admissions=[]
for row in checks['cases']:
 case=row['case'];saved=[(Q(e['time_s']),Q(e['delta_m'])) for e in row['accepted_events']]
 assert defs[case]==saved
 assert peak(Q(1,5),saved,Q(0))==Q(row['exact_reference_jerk_peak_m_s3'])
 finals.append({'case':case,'events':len(saved),'peak':row['exact_reference_jerk_peak_m_s3']})
 es=[];target=Q(0)
 for i,o in enumerate(row['outcomes']):
  if o['outcome'] not in ('accepted','jerk_rejected'):continue
  name=f'{case}_admission_{i}'; c,actual,want=evals[name]
  assert c==Q(o['commit_s'])
  d=Q(o['target_m'])-target;candidate=es+([(c,d)] if d else [])
  assert actual==candidate
  pk=peak(Q(1,5),candidate,c)
  ok=pk<=Q(15,2)
  assert want==ok==(o['outcome']=='accepted')
  assert pk==Q(o['future_reference_jerk_peak_m_s3'])
  if ok:es=candidate;target=Q(o['target_m'])
  admissions.append({'name':name,'passed':ok,'peak':str(pk)})
source_hashes={}
for folder in ['lead-01','ultra-preflight-02']:
 manifest=json.loads((POD/folder/'artifact-sha256.json').read_text())
 for name,h in manifest['files'].items():
  assert sha(POD/folder/name)==h
  source_hashes[f'{folder}/{name}']=h
result={'passed':True,'literal_final_history_bindings':finals,'literal_admission_bindings':admissions,'frozen_input_hashes':source_hashes,'fixture_source_sha256':sha(BUILDER/'Fixtures.lean'),'scope':'Independent exact fixture binding and derivative arithmetic; no copied generator or checker.'}
(HERE/'binding-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'final_histories':len(finals),'admissions':len(admissions),'frozen_inputs':len(source_hashes)}))
