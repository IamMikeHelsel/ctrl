#!/usr/bin/env python3
"""Translate frozen E5 nodes into explicit closed-child Lean proof applications.
The generator is untrusted. All bounds and parent-child types are kernel checked.
"""
from pathlib import Path
from fractions import Fraction
import json,hashlib
H=Path(__file__).resolve().parent
raw=(H/'inputs/certificate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='130162c84e4e7c899cf873e40cbad19bccad8d836afe86013beea700fd2e8dfb'
d=json.loads(raw);nodes=d['nodes'];assert len(nodes)==1743
q=lambda v:'('+str(Fraction(v).numerator)+' / '+str(Fraction(v).denominator)+' : ℚ)'
lines=['import SelectorSemantics','set_option maxRecDepth 10000','set_option maxHeartbeats 20000000','namespace E10']
counts={}
for i in reversed(range(len(nodes))):
 n=nodes[i];cl,ch=map(q,n['c']);jl,jh=map(q,n['j']);cb=f'({cl},{ch})';jb=f'({jl},{jh})';method=n['method'];counts[method]=counts.get(method,0)+1
 lines.append(f'theorem node_{i} : Covered {cb} {jb} := by')
 if method=='split':
  mid=q(n['midpoint']);a,b=n['children']
  lines.append(f' exact split_{n["axis"]} {cl} {ch} {jl} {jh} {mid} node_{a} node_{b}')
 else:
  lines.append(' intro c j hc hj')
  if method=='uniform':lines.append(' exact uniform_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)')
  elif method=='completion':lines.append(' exact completion_sound hc hj (by decide +kernel) (by decide +kernel) (by decide +kernel)')
  elif method=='moment':
   t=q(n['theta']);lines.append(f' exact moment_sound (t := {t}) hc hj (by decide +kernel)')
  else:raise ValueError(n)
lines+=['theorem middle : Covered (767/1000,22/25) (0,I) := node_0','end E10']
(H/'CheckedTree.lean').write_text('\n'.join(lines)+'\n')
(H/'generated-data.json').write_text(json.dumps({'input_sha256':hashlib.sha256(raw).hexdigest(),'node_count':len(nodes),'methods':counts,'output_sha256':hashlib.sha256((H/'CheckedTree.lean').read_bytes()).hexdigest()},indent=2)+'\n')
print(counts)
