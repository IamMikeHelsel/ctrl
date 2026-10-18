#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3];BASE=ROOT/'lean-controls';CHECKER=HERE.parent
env=os.environ.copy();env['ELAN_HOME']=str(ROOT/'.tools/elan')
lake=str(ROOT/'.tools/elan/bin/lake')
read=lambda args:subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
lean=read(['which','lean']);deps=read(['printenv','LEAN_PATH'])
deps=':'.join(str((BASE/p).resolve())if not Path(p).is_absolute()else p for p in deps.split(':'))
env['LEAN_PATH']=':'.join([str(HERE),str(CHECKER),str(CHECKER.parent/'recovery-proof'),deps])
env['PATH']=str(Path(lean).parent)+':'+env.get('PATH','')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
path=HERE/'benchmark.json'
report=json.loads(path.read_text())if path.exists()else{
 'scope':'fresh new probe modules; reuse existing checker and frozen main/mathlib dependency artifacts; individual kernel replay, not full dependency replay',
 'toolchain':read(['lean','--version']),
 'unchanged_reference_source_sha256':{n:sha(CHECKER/n)for n in ('IntervalPilot.lean','IntervalChecker.lean','pilot-data.json','coefficient-data.json')},'runs':[]}
for module in sys.argv[1:]:
 result={'module':module,'source_sha256':sha(HERE/(module+'.lean')),'operations':[]}
 for name,cmd in [('compile',[lean,'--root='+str(HERE),'-o',str(HERE/(module+'.olean')),str(HERE/(module+'.lean'))]),
                  ('kernel',[str(Path(lean).with_name('leanchecker')),module,'-v'])]:
  log=HERE/(module+'-'+name+'.log');start=time.monotonic()
  with log.open('w')as f:
   try:run=subprocess.run(cmd,cwd=HERE,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90);code=run.returncode
   except subprocess.TimeoutExpired:code='timeout90s'
  op={'operation':name,'seconds':time.monotonic()-start,'exit_code':code,'log_sha256':sha(log)}
  result['operations'].append(op);print(module,name,code,round(op['seconds'],3),flush=True)
  if code!=0:break
 if result['operations'][0]['exit_code']==0:
  text=(HERE/(module+'-compile.log')).read_text()
  matches=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
  none=re.findall(r"'([^']+)' does not depend on any axioms",text)
  result['axioms']={n:[a.strip()for a in aa.split(',')if a.strip()]for n,aa in matches}
  result['axioms'].update({n:[]for n in none})
  result['axiom_gate']=bool(result['axioms'])and all(set(a)<={'propext','Classical.choice','Quot.sound'}for a in result['axioms'].values())
 report['runs'].append(result)
 report['reference_sources_unchanged']=all(sha(CHECKER/n)==v for n,v in report['unchanged_reference_source_sha256'].items())
 path.write_text(json.dumps(report,indent=2)+'\n')
