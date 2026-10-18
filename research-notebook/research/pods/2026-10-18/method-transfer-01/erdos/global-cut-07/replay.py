#!/usr/bin/env python3
"""Fresh copied-source replay of the fixed E7 sample and independent checks."""
from pathlib import Path
import datetime,hashlib,json,platform,shutil,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 evidence=HERE/'evidence';evidence.mkdir(exist_ok=True)
 fresh=Path(tempfile.mkdtemp(prefix='copied-source-',dir=evidence));hashes={}
 for name in ['screen.py','diagnostic.py','verify.py','INPUT-CONFIG.json']:
  shutil.copyfile(HERE/name,fresh/name);hashes[name]=sha(fresh/name)
  assert hashes[name]==sha(HERE/name)
 jobs=[('screen.py','screen-results.json','screen.stderr'),
       ('diagnostic.py','coverage-diagnostic.json','diagnostic.stderr'),
       ('verify.py','verification.json','verification.stderr')]
 records=[]
 for source,outname,errname in jobs:
  rec={'command':[sys.executable,source],'cwd':str(fresh),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'timeout_seconds':60,'termination_grace_seconds':5,'remote':False}
  with (fresh/outname).open('w') as out,(fresh/errname).open('w') as err:
   proc=subprocess.Popen(rec['command'],cwd=fresh,stdout=out,stderr=err);rec['pid']=proc.pid
   try:rec['exit_code']=proc.wait(timeout=60);rec['terminated']=False
   except subprocess.TimeoutExpired:
    rec['terminated']=True;proc.terminate()
    try:rec['exit_code']=proc.wait(timeout=5)
    except subprocess.TimeoutExpired:proc.kill();rec['exit_code']=proc.wait();rec['killed_after_grace']=True
  rec['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
  rec['stdout']=outname;rec['stderr']=errname;rec['stdout_sha256']=sha(fresh/outname);rec['stderr_sha256']=sha(fresh/errname)
  records.append(rec);assert rec['exit_code']==0,(source,rec)
 a=json.loads((HERE/'screen-results.json').read_text());b=json.loads((fresh/'screen-results.json').read_text())
 a.pop('seconds');b.pop('seconds');assert a==b,'fixed-screen mathematics changed'
 assert (HERE/'coverage-diagnostic.json').read_bytes()==(fresh/'coverage-diagnostic.json').read_bytes()
 assert (HERE/'verification-development.json').read_bytes()==(fresh/'verification.json').read_bytes()
 report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,
  'platform':platform.platform(),'inputs':hashes,'commands':records,'passed':True,
  'mathematical_output_matches':True,'excluded_from_equality':['seconds'],
  'diagnostic_matches':True,'independent_verification_matches':True,'new_samples':0}
 (fresh/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'fresh_directory':str(fresh),'replay_sha256':sha(fresh/'replay.json'),'passed':True},indent=2))
if __name__=='__main__':main()
