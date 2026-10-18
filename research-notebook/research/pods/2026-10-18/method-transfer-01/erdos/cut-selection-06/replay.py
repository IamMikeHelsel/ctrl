#!/usr/bin/env python3
"""Copy source into a fresh directory and replay all E6 evidence."""
from pathlib import Path
import datetime,hashlib,json,platform,shutil,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 evidence=HERE/'evidence';evidence.mkdir(exist_ok=True)
 fresh=Path(tempfile.mkdtemp(prefix='copied-source-',dir=evidence))
 sources=['experiment.py','verify.py'];hashes={}
 for name in sources:
  shutil.copyfile(HERE/name,fresh/name)
  hashes[name]=digest(fresh/name)
  assert hashes[name]==digest(HERE/name)
 jobs=[('experiment.py','results-development.json','experiment.stderr'),
       ('verify.py','verification.json','verification.stderr')]
 records=[]
 for source,output,error in jobs:
  command=[sys.executable,source]
  with (fresh/output).open('w') as out,(fresh/error).open('w') as err:
   done=subprocess.run(command,cwd=fresh,stdout=out,stderr=err,timeout=180,check=False)
  records.append({'command':command,'cwd':str(fresh),'exit_code':done.returncode,
                  'stdout':output,'stderr':error,'stdout_sha256':digest(fresh/output),
                  'stderr_sha256':digest(fresh/error)})
  assert done.returncode==0,(source,done.returncode)
 a=json.loads((HERE/'results-development.json').read_text())
 b=json.loads((fresh/'results-development.json').read_text())
 a.pop('seconds');b.pop('seconds')
 assert a==b,'fresh mathematical outputs changed'
 verified=json.loads((fresh/'verification.json').read_text())
 assert verified==json.loads((HERE/'verification-development.json').read_text())
 assert verified['passed'] and all(x['rejected'] for x in verified['negative_controls'])
 report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'python':sys.version,'platform':platform.platform(),'source_sha256':hashes,
         'commands':records,'fresh_mathematical_output_matches':True,
         'excluded_from_equality':['seconds'],'verification_matches':True,
         'passed':True,'no_external_dependencies':True}
 (fresh/'replay.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'fresh_directory':str(fresh),'replay_sha256':digest(fresh/'replay.json'),
                   'passed':True},indent=2))
if __name__=='__main__':main()
