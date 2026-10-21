#!/usr/bin/env python3
"""Fresh copied-source B1 replay. No old build products or downloaded packages."""
import argparse,hashlib,json,shutil,subprocess,sys,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
base=Path(__file__).resolve().parent;a.output.mkdir(parents=True,exist_ok=False)
src=a.output/'source';src.mkdir();bindings={}
for name in ['compare.py','controls.py','terminal_interval.py','inputs.json']:
 shutil.copy2(base/name,src/name);bindings[name]=hashlib.sha256((src/name).read_bytes()).hexdigest()
commands=[('terminal',[sys.executable,str(src/'terminal_interval.py'),'--output',str(a.output/'terminal-exact.json')]),
          ('controls',[sys.executable,str(src/'controls.py'),'--output',str(a.output/'controls.json')]),
          ('comparison',[sys.executable,str(src/'compare.py'),'--output',str(a.output/'results')])]
records=[]
for name,cmd in commands:
 t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
 (a.output/f'{name}.log').write_text(r.stdout+r.stderr)
 records.append({'name':name,'returncode':r.returncode,'seconds':time.monotonic()-t,'command':cmd})
 assert r.returncode==0,records[-1]
summary=json.loads((a.output/'results/summary.json').read_text());controls=json.loads((a.output/'controls.json').read_text());tail=json.loads((a.output/'terminal-exact.json').read_text())
checks={'24_runs':len(summary['results'])==24,'14_controls':len(controls['checks'])==14 and all(controls['checks'].values()),'8_exact_tail_checks':len(tail['checks'])==8 and all(tail['checks'].values()),
        'same_requested_target':all(x['requested_position']==.14 for x in summary['results']),
        'RG_no_clipping':all(x['clip_count']==0 for x in summary['results'] if x['controller']=='RG'),
        'no_numerical_travel_violations':all(x['forward_margin']>=0 and x['lower_margin']>=0 for x in summary['results'])}
# Compare complete deterministic outputs against preserved development run, when present.
old=base/'development-full/summary.json'
if old.exists():
 prior=json.loads(old.read_text())
 def stable(rows):return [{k:v for k,v in x.items() if k!='elapsed_seconds'} for x in rows]
 checks['fresh_results_equal_development']=stable(prior['results'])==stable(summary['results'])
if (base/'terminal-exact.json').exists():checks['fresh_exact_tail_equals_development']=tail==json.loads((base/'terminal-exact.json').read_text())
result={'copied_source_sha256':bindings,'commands':records,'checks':checks,'passed':all(checks.values()),'scope':'Independent copied-source execution by builder; independent acceptance belongs to root.'}
(a.output/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['checks'],indent=2));assert result['passed']
