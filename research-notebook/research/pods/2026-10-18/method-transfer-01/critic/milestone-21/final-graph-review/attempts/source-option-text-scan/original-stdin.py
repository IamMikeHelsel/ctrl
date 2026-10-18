import json,re
from pathlib import Path
h=Path('research/pods/2026-10-18/method-transfer-01/critic/milestone-21/final-graph-review')
b=h/'builder-copy';c=json.loads((b/'complete-closure.json').read_text())
opts={}; hazards=[]
for mod,d in c['modules'].items():
 s=(b/d['source']).read_text()
 for n,v in re.findall(r'(?m)^\s*set_option\s+(\S+)\s+([^\n]+)',s):opts.setdefault(n,set()).add(v)
 for key in ['skipKernelTC','implemented_by','extern','axiom ','unsafe ','native_decide','trustCompiler']:
  if key in s:hazards.append((mod,key))
print('Options:',{k:sorted(v) for k,v in opts.items()});print('Hazard text matches:',hazards)
d={'options':{k:sorted(v) for k,v in opts.items()},'hazard_text_matches':hazards,'note':'No kernel-skipping option or executable proof escape found in the 34 local source modules. Separate kernel replay is the primary check.'}
assert not hazards
(h/'source-options-check.json').write_text(json.dumps(d,indent=2)+'\n')
