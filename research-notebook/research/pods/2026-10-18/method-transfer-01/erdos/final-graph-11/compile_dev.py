#!/usr/bin/env python3
from pathlib import Path
import os,sys,subprocess,time,json,shutil,tempfile
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-controls').is_dir())
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
WORK=HERE/'development'
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[WORK,*sorted(p/'.lake/build/lib/lean' for p in (ROOT/'lean-controls/.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir())]))
for mod in sys.argv[1:]:
 rel=Path(mod.replace('.','/')).with_suffix('.lean')
 src=HERE/rel
 if src.exists():shutil.copyfile(src,WORK/rel)
 attempt=Path(tempfile.mkdtemp(prefix='attempt-'+mod.replace('.','-')+'-',dir=HERE))
 shutil.copyfile(WORK/rel,attempt/rel.name)
 start=time.monotonic()
 p=subprocess.run([str(BIN/'lean'),'-o',str(rel.with_suffix('.olean')),str(rel)],cwd=WORK,env=env,capture_output=True,text=True)
 (attempt/'compile.log').write_text(p.stdout+p.stderr)
 (attempt/'run.json').write_text(json.dumps({'module':mod,'exit':p.returncode,'seconds':time.monotonic()-start},indent=2)+'\n')
 print(mod,p.returncode,attempt.name,flush=True);print(p.stdout+p.stderr,flush=True)
 if p.returncode:sys.exit(p.returncode)
