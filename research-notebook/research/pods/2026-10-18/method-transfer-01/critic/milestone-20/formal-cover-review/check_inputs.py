#!/usr/bin/env python3
"""Independent freeze, regeneration, exact tree and local dependency audit."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import json,hashlib,re,shutil,subprocess,datetime
D=Path(__file__).resolve().parent;B=D/'builder-copy'
ROOT=next(p for p in D.parents if (p/'lean-controls').is_dir())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((B/'INPUTS.json').read_text());past=[]
for entry in prov['prior_freezes']:
 p=ROOT/entry['manifest'];assert sha(p)==entry['sha256']
 rows=json.loads(p.read_text())['files']
 for rel,h in rows.items():assert sha(p.parent/rel)==h,(p,rel)
 past.append({'manifest':entry['manifest'],'sha256':sha(p),'files':len(rows)})
for r in prov['copies']:
 assert sha(ROOT/r['original'])==r['sha256']==sha(B/r['copy']),r['copy']
for r in prov['unchanged_dependencies']:
 assert sha(ROOT/r['original'])==r['sha256']==sha(B/r['copy']),r['copy']
cert=B/'inputs/certificate.json'
assert sha(cert)=='130162c84e4e7c899cf873e40cbad19bccad8d836afe86013beea700fd2e8dfb'
original=ROOT/'research/pods/2026-10-18/method-transfer-01/erdos/free-slope-05/certificate.json'
assert cert.read_bytes()==original.read_bytes()
G=D/'regeneration';(G/'inputs').mkdir(parents=True,exist_ok=True)
shutil.copyfile(cert,G/'inputs/certificate.json');shutil.copyfile(B/'generate_tree.py',G/'generate_tree.py')
p=subprocess.run(['python3','generate_tree.py'],cwd=G,capture_output=True,text=True)
(G/'generator.log').write_text(p.stdout+p.stderr);assert p.returncode==0
assert (G/'CheckedTree.lean').read_bytes()==(B/'CheckedTree.lean').read_bytes()
assert (G/'generated-data.json').read_bytes()==(B/'generated-data.json').read_bytes()
nodes=json.loads(cert.read_text())['nodes'];seen=set();parents=Counter();leaves=[];counts=Counter();slopes=Counter()
def pair(v):return tuple(F(x) for x in v)
def visit(i,cb,jb):
 assert i not in seen;seen.add(i);n=nodes[i]
 assert pair(n['c'])==cb and pair(n['j'])==jb
 assert cb[0]<cb[1] and jb[0]<jb[1]
 counts[n['method']]+=1
 if n['method']=='split':
  l,r=n['children'];assert i<l<len(nodes) and i<r<len(nodes);parents[l]+=1;parents[r]+=1
  m=F(n['midpoint'])
  if n['axis']=='c':assert cb[0]<m<cb[1];visit(l,(cb[0],m),jb);visit(r,(m,cb[1]),jb)
  else:assert n['axis']=='j' and jb[0]<m<jb[1];visit(l,cb,(jb[0],m));visit(r,cb,(m,jb[1]))
 else:
  assert n['method'] in ('uniform','completion','free_moment');leaves.append(i)
  if n['method']=='free_moment':slopes[str(F(n['theta']))]+=1
visit(0,(F(767,1000),F(22,25)),(F(0),F(2,47)))
assert seen==set(range(1743));assert parents==Counter({i:1 for i in range(1,1743)})
assert len(leaves)==872
assert counts=={'uniform':53,'completion':250,'free_moment':569,'split':871}
assert slopes=={'0':205,'1':364}
# Independently resolve every import from the exact copied local sources.
module_names=['Erdos128.WeightedGraph','Erdos128.CubicNeighborhood','Erdos128.OneStepSaving','WeightedProfiles','SquareCertificate','RationalIntervals','SelectorSemantics','CheckedTree','UniversalSelector','SelectorControls']
imports={};declarations={};allnames=[]
for name in module_names:
 rel=Path(name.replace('.','/')).with_suffix('.lean');txt=(B/rel).read_text()
 im=[]
 for line in txt.splitlines():
  m=re.match(r'^(?:public\s+)?import\s+(.*)',line)
  if m:im+=m[1].split()
 for dep in im:assert dep=='Mathlib' or dep in module_names
 imports[name]=im
 # Count public declarations independently from their leading lexical keywords.
 stack=[];ds=[]
 for line in txt.splitlines():
  m=re.match(r'^namespace\s+(\S+)\s*$',line)
  if m:stack.append(m[1]);continue
  m=re.match(r'^end\s+(\S+)\s*$',line)
  if m and stack and m[1]==stack[-1]:stack.pop();continue
  m=re.match(r'^(?:@\[[^\]]+\]\s*)?(theorem|lemma)\s+(\w+)',line)
  if m:ds.append('.'.join(stack+[m[2]]))
 declarations[name]=ds;allnames+=ds
assert len(allnames)==len(set(allnames))==1821
assert len(declarations['CheckedTree'])==1744
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Independent source and exact tree checks; proof acceptance requires separate fresh build/audit/kernel evidence','prior_freezes':past,'prior_entries':sum(r['files'] for r in past),'source_copies_and_dependency_pins_match':True,'certificate_sha256':sha(cert),'regenerated_tree_sha256':sha(G/'CheckedTree.lean'),'regeneration_byte_identical':True,'nodes':len(seen),'leaves':len(leaves),'methods':dict(counts),'moment_thetas':dict(slopes),'closed_child_geometry_and_single_parent':True,'all_nodes_reachable':True,'imports':imports,'declarations_by_module':{k:len(v) for k,v in declarations.items()},'declarations':allnames}
(D/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('declarations','imports','prior_freezes')},indent=2))
