#!/usr/bin/env python3
"""Reproduce the fixed screen in an isolated folder and compare frozen evidence."""
from pathlib import Path
import json,hashlib,os,sys,subprocess,tempfile,shutil,time
HERE=Path(__file__).resolve().parent;WORK=HERE.parents[4]
HPPY=WORK/'.tools/research-python/bin/python'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canonical(p):
 r=json.loads(p.read_text());r.pop('seconds',None);return r
scripts=['screen.py','crosscheck.py','check_equations.py']
inputs={s:sha(HERE/s)for s in scripts}
logs=HERE/'verification-logs';logs.mkdir(exist_ok=True)
report={'passed':False,'source_sha256':inputs,'steps':[],'checks':{}}
def save():(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
with tempfile.TemporaryDirectory(prefix='replay-',dir=HERE)as tmp:
 root=Path(tmp)
 for s in scripts:shutil.copy2(HERE/s,root/s)
 for label,exe,script in [('scipy-screen',sys.executable,'screen.py'),('exact-equations',sys.executable,'check_equations.py'),('mpmath-all-samples',str(HPPY),'crosscheck.py')]:
  start=time.monotonic()
  with (logs/(label+'.log')).open('w')as f:p=subprocess.run([exe,str(root/script)],stdout=f,stderr=subprocess.STDOUT,timeout=180)
  report['steps'].append({'label':label,'exit_code':p.returncode,'seconds':time.monotonic()-start,'log_sha256':sha(logs/(label+'.log'))});save();assert p.returncode==0,label
 files=['screen-result.json','continuity-checks.json','equilibrium-checks.json','high-precision-check.json','equations-check.json']
 report['checks']['json_content_matches_excluding_elapsed_seconds']={f:canonical(root/f)==canonical(HERE/f)for f in files}
 report['checks']['summary_csv_byte_match']=sha(root/'summary.csv')==sha(HERE/'summary.csv')
 traces=sorted((HERE/'traces').glob('*.csv'));assert len(traces)==48
 report['checks']['all_48_trace_hashes_match']=all(sha(p)==sha(root/'traces'/p.name)for p in traces)
 report['checks']['sources_unchanged']=all(sha(HERE/s)==h for s,h in inputs.items())
 report['trace_sha256']={p.name:sha(p)for p in traces}
 report['passed']=all(report['checks']['json_content_matches_excluding_elapsed_seconds'].values()) and all(v for k,v in report['checks'].items()if k!='json_content_matches_excluding_elapsed_seconds')
 save();assert report['passed'];print(json.dumps({'passed':True,'cases':48,'rows':canonical(HERE/'high-precision-check.json')['samples_checked'],'trace_hashes_match':True}))
