#!/usr/bin/env python3
import json,re
from pathlib import Path
from check_inputs import strip_comments
H=Path(__file__).resolve().parent
B=H/'builder-copy'
closure=json.loads((B/'complete-closure.json').read_text())
options={}; hazards=[]
for mod,item in closure['modules'].items():
    txt=strip_comments((B/item['source']).read_text())
    for key,value in re.findall(r'(?m)^\s*set_option\s+(\S+)\s+([^\n]+)',txt):
        options.setdefault(key,set()).add(value)
    bad=re.findall(r'\b(?:skipKernelTC|implemented_by|extern|axiom|unsafe|native_decide|trustCompiler)\b',txt)
    hazards.extend((mod,b) for b in bad)
assert not hazards,hazards
result={'passed':True,'local_modules':len(closure['modules']),'options':{k:sorted(v) for k,v in options.items()},'hazards':hazards,'replacement_for':'attempts/source-option-text-scan/original-stdin.py','scope':'Auxiliary whole-token source scan after stripping comments. Does not replace the full axiom audit or separate kernel replay.'}
(H/'source-options-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
