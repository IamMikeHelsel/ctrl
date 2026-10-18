"""Run independent exact expected decisions against both fresh Lean checkers."""
from pathlib import Path
import json,subprocess,os,time
p=Path(__file__).resolve().parent
r=json.loads((p/'rebuild.json').read_text());env=os.environ.copy();env['LEAN_PATH']=r['lean_path'];t=time.monotonic()
a=subprocess.run([r['builds'][0]['command'][0],'--run',str(p/'DecisionReplay.lean')],cwd=p/'.cache/fresh',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(p/'decision-run.log').write_text(a.stdout)
assert a.returncode==0,a.stdout[-4000:]
expected=json.loads((p/'oracle-results.json').read_text())['decisions'];got=a.stdout.strip().splitlines();assert len(got)==len(expected)
for row,e in zip(got,expected):
 i,x,y=row.split('|');assert int(i)==e['id'] and (x=='true')==e['expected'] and (y=='true')==e['expected']
(p/'decision-review.json').write_text(json.dumps({'status':'PASS','decisions':len(expected),'both_Lean_checkers_agree_with_independent_oracle':True,'seconds':time.monotonic()-t},indent=2)+'\n')
print('PASS',len(got))
