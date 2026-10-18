#!/usr/bin/env python3
"""Fresh copied-source exact replay. Every run preserves its own evidence."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess,sys,tempfile,time
HERE=Path(__file__).resolve().parent
FILES=['build_cover.py','verify_cover.py','mathematical_controls.py']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(HERE/'evidence').mkdir(exist_ok=True)
work=Path(tempfile.mkdtemp(prefix='copied-source-',dir=HERE/'evidence'))
sources={}
for name in FILES:
 shutil.copyfile(HERE/name,work/name);sources[name]=sha(HERE/name)
result={'started_utc':datetime.now(timezone.utc).isoformat(),'work':str(work.relative_to(HERE)),
        'python':sys.version,'source_hashes':sources,'runs':[],'passed':False}
def save():
 (work/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
for script,out in [('build_cover.py','generation'),('verify_cover.py','verification'),('mathematical_controls.py','mathematical-controls')]:
 started=time.monotonic();command=[sys.executable,script]
 try:
  p=subprocess.run(command,cwd=work,text=True,capture_output=True,timeout=120)
  code=p.returncode;stdout=p.stdout;stderr=p.stderr
 except subprocess.TimeoutExpired as exc:
  code=124;stdout=str(exc.stdout or '');stderr=str(exc.stderr or '')+'\nTIMEOUT'
 (work/(out+'.json')).write_text(stdout);(work/(out+'.stderr')).write_text(stderr)
 result['runs'].append({'script':script,'command':command,'exit':code,'seconds':time.monotonic()-started,'output':out+'.json','stderr':out+'.stderr'})
 save()
 if code:raise SystemExit(code)
 # Require valid JSON, not just process success.
 data=json.loads(stdout)
 if script!='mathematical_controls.py':assert data['passed']
a=json.loads((HERE/'certificate.json').read_text());b=json.loads((work/'certificate.json').read_text())
a.pop('recorded_utc');b.pop('recorded_utc');assert a==b
assert json.loads((HERE/'verification-development.json').read_text())==json.loads((work/'verification.json').read_text())
assert json.loads((HERE/'mathematical-controls-development.json').read_text())==json.loads((work/'mathematical-controls.json').read_text())
assert all(sha(HERE/name)==sha(work/name)==h for name,h in sources.items())
result.update({'passed':True,'completed_utc':datetime.now(timezone.utc).isoformat(),
               'certificate_matches_except_timestamp':True,'verification_matches':True,
               'mathematical_controls_match':True,'source_hashes_stable':True,
               'outputs_sha256':{q.name:sha(q) for q in sorted(work.iterdir()) if q.is_file() and q.name!='replay.json'}})
save();print(json.dumps({'passed':True,'work':str(work),'replay_sha256':sha(work/'replay.json')},indent=2))
