"""Root's direct edge-sum audit. Does not import either builder implementation."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]
d=json.loads((HERE/'inputs/screen-results.json').read_text())
graphs={h['name']:h for h in d['hosts']}
summary=[];uniform=[];internal=[];cuts=0;orientations=0;tiescount=0
for c in d['cases']:
 h=graphs[c['host']];n=h['n'];E=[tuple(e) for e in h['edges']];a=c['integer_weights'];W=sum(a)
 assert len(set(E))==len(E) and all(0<=u<v<n for u,v in E)
 adj=[set() for _ in a]
 for u,v in E:adj[u].add(v);adj[v].add(u)
 assert all(not(adj[u]&adj[v]) for u,v in E)
 best=None;ties=[]
 for mask in range(0,1<<n,2):
  value=sum(a[u]*a[v] for u,v in E if bool(mask&(1<<u))==bool(mask&(1<<v)))
  cuts+=1
  if best is None or value<best:best=value;ties=[mask]
  elif value==best:ties.append(mask)
 assert best==c['minimum_internal_numerator'] and ties==c['global_tie_masks']
 assert 47*best<=2*W*W
 internal.append(F(best,W*W));tiescount+=len(ties)
 for mask in ties:
  mass=sum(a[v] for v in range(n) if mask&(1<<v));full=(1<<n)-1
  xs=[mask] if 2*mass<W else [full^mask] if 2*mass>W else [mask,full^mask]
  for x in xs:
   y=full^x;Y=sum(a[v] for v in range(n) if y&(1<<v))
   J=sum(a[u]*a[v] for u,v in E if y&(1<<u) and y&(1<<v))
   cost=F(J,4*Y*Y);uniform.append(cost);orientations+=1
   assert cost<=F(1,40)
 counts=c['true_fractional_half']['selected_vertex_counts']
 assert sum(counts)==W and all(0<=z<=2*w for z,w in zip(counts,a))
 value=F(sum(counts[u]*counts[v] for u,v in E),4*W*W)
 assert value==F(c['true_fractional_half']['cost'])<=F(1,50)
 summary.append({'host':c['host'],'pattern':c['weight_pattern'],'ties':len(ties),'half_witness_cost':str(value)})
assert cuts==655104 and tiescount==120 and orientations==146
assert max(uniform)==F(9,392) and max(internal)==F(4,121)
inputs=json.loads((HERE/'inputs/INPUTS.json').read_text());preserved=0
for f in inputs['files']:
 assert hashlib.sha256((WORK/f['path']).read_bytes()).hexdigest()==f['sha256']
for freeze in inputs['prior_freezes']:
 p=WORK/freeze['manifest'];assert hashlib.sha256(p.read_bytes()).hexdigest()==freeze['sha256']
 m=json.loads(p.read_text())
 for name,sha in m['files'].items():
  assert hashlib.sha256((p.parent/name).read_bytes()).hexdigest()==sha;preserved+=1
assert preserved==209
print(json.dumps({'passed':True,'method':'direct sum over every edge for each cut; actual integer-half witness costs','cases':summary,'cuts':cuts,'ties':tiescount,'orientations':orientations,'max_uniform_cost':str(max(uniform)),'max_internal_cost':str(max(internal)),'prior_files_intact':preserved,'scope':'All atomic-support ties and positive finite-blowup witnesses, not classification of split-cluster ties or universal graph theorem'},indent=2))
