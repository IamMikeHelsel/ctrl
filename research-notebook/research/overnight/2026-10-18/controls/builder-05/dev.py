from pathlib import Path
import os,re,shutil,subprocess,sys
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
BASE=WORK/'lean-controls'
def source_closure(target='FIRHoldWitness'):
 result={}
 def visit(m):
  if m in result:return
  p=HERE/(m+'.lean')
  if not p.exists():p=HERE/'inherited'/(m.replace('.','/')+'.lean')
  if not p.exists():return
  for d in re.findall(r'^(?:public )?import (\S+)',p.read_text(),re.M):visit(d)
  result[m]=p
 visit(target);return result
def environment():
 env=os.environ.copy();env['ELAN_HOME']=str(WORK/'.tools/elan')
 lake=str(WORK/'.tools/elan/bin/lake')
 def query(*args):return subprocess.check_output([lake,'env',*args],cwd=BASE,env=env,text=True).strip()
 lean=query('which','lean')
 deps=':'.join(str((BASE/p).resolve()) if not Path(p).is_absolute() else p for p in query('printenv','LEAN_PATH').split(':'))
 deps=':'.join(p for p in deps.split(':') if str(BASE/'.lake/build') not in p)
 return env,lean,deps
def main():
 target=sys.argv[1] if len(sys.argv)>1 else 'FIRHoldWitness'
 env,lean,deps=environment();root=HERE/'build';root.mkdir(exist_ok=True)
 env['LEAN_PATH']=str(root)+':'+deps
 env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
 for m,p in source_closure(target).items():
  dst=root/(m.replace('.','/')+'.lean');out=dst.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  if dst.exists() and out.exists() and dst.read_bytes()==p.read_bytes():continue
  shutil.copyfile(p,dst); print('BUILD',m,flush=True)
  p=subprocess.run([lean,'--root='+str(root),'-o',str(out),str(dst)],cwd=root,env=env)
  if p.returncode:sys.exit(p.returncode)
if __name__=='__main__':main()
