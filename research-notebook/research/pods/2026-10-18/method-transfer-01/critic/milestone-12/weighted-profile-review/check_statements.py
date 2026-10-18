from pathlib import Path
import re,json,difflib
p=Path(__file__).resolve().parent;b=p/'frozen-builder'
def statements(path):
 return {n:' '.join(t.split()) for n,t in re.findall(r'^theorem\s+(\w+)(.*?):=',path.read_text(),re.M|re.S)}
r={}
for name,old,new in [('builder_main','attempt-WeightedProfiles-hg2627oz/WeightedProfiles.lean','WeightedProfiles.lean'),('builder_controls','attempt-ProfileControls-eo_0hwt8/ProfileControls.lean','ProfileControls.lean')]:
 x,y=statements(b/old),statements(b/new)
 r[name]={'common':len(x.keys()&y.keys()),'changed_statements':sorted(n for n in x.keys()&y.keys() if x[n]!=y[n]),'added':sorted(y.keys()-x.keys()),'removed':sorted(x.keys()-y.keys())}
a=p/'attempts/critic-moment-unfold/CriticControls.lean';c=p/'CriticControls.lean';x,y=statements(a),statements(c)
r['critic_repair']={'common':len(x.keys()&y.keys()),'changed_statements':sorted(n for n in x.keys()&y.keys() if x[n]!=y[n]),'added':sorted(y.keys()-x.keys()),'removed':sorted(x.keys()-y.keys())}
assert all(not x['changed_statements'] and not x['removed'] for x in r.values())
(p/'critic-repair.diff').write_text(''.join(difflib.unified_diff(a.read_text().splitlines(True),c.read_text().splitlines(True),fromfile='failed CriticControls.lean',tofile='repaired CriticControls.lean')))
(p/'statement-preservation.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
