from pathlib import Path
import os,subprocess,sys
here=Path(__file__).resolve().parent
root=here.parents[2]
bin=Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0/bin'
packages=root/'lean-controls/.lake/packages'
deps=sorted(p/'.lake/build/lib/lean' for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir())
env=os.environ.copy();env['PATH']=str(bin)+os.pathsep+env.get('PATH','')
env['LEAN_PATH']=os.pathsep.join(map(str,[here,here.parent/'erdos-bridge-spike',*deps]))
module=sys.argv[1] if len(sys.argv)>1 else 'CompletionBranch'
p=subprocess.run([str(bin/'lean'),'-o',module+'.olean',module+'.lean'],cwd=here,env=env,text=True,capture_output=True)
(here/(module+'.log')).write_text(p.stdout+p.stderr)
print(p.stdout+p.stderr)
sys.exit(p.returncode)
