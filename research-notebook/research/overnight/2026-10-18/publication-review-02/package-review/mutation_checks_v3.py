from pathlib import Path
import copy,hashlib,json,shutil,subprocess
R=Path(__file__).resolve().parent; W=R.parents[4]
P=R/'package-v3'; D=W/'lean-controls'; M=R/'mutants-v3'; M.mkdir(exist_ok=True)
results=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def package(name):
 q=M/name; shutil.copytree(P,q,ignore=shutil.ignore_patterns('__pycache__'));return q
def rehash(q):
 p=q/'input-manifest.json'; x=json.loads(p.read_text()); x['files']={f:sha(q/f) for f in x['files'] if (q/f).is_file()};p.write_text(json.dumps(x,indent=2)+'\n')
def run(name,q,dep=D):
 cmd=['python3',str(q/'replay.py'),'--dependency-project',str(dep),'--lake',str(W/'.tools/elan/bin/lake'),'--elan-home',str(W/'.tools/elan'),'--output',str(M/(name+'-unused-output')),'--check-inputs-only']
 p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(M/(name+'.log')).write_text(p.stdout)
 results.append({'name':name,'exit_code':p.returncode,'accepted':p.returncode==0,'command':cmd,'tail':p.stdout.splitlines()[-1] if p.stdout else ''}); print(name,p.returncode,results[-1]['tail'],flush=True)
q=package('source-rehashed');s=q/'src/FutureCommit.lean';s.write_text(s.read_text()+'\n-- changed original source bytes\n');rehash(q);run('source-rehashed',q)
for name,change in [('roots-rehashed',lambda x:x['roots'].pop()),('kernel-empty-rehashed',lambda x:x.__setitem__('kernel_targets',[])),('negative-removed-rehashed',lambda x:x['negative_controls'].pop(next(iter(x['negative_controls']))))]:
 q=package(name); f=q/'source-bindings.json';x=json.loads(f.read_text());change(x);f.write_text(json.dumps(x,indent=2)+'\n');rehash(q);run(name,q)
q=package('pin-package-rehashed');f=q/'dependency-project/lakefile.toml';f.write_text(f.read_text()+'\n# changed pin bytes\n');rehash(q);run('pin-package-rehashed',q)
q=package('pin-both-rehashed');f=q/'dependency-project/lakefile.toml';f.write_text(f.read_text()+'\n# changed pin bytes\n');rehash(q)
d=M/'changed-dependency-project';d.mkdir();
for name in ('lean-toolchain','lakefile.toml','lake-manifest.json'):shutil.copyfile(q/'dependency-project'/name,d/name)
(d/'.lake').symlink_to(D/'.lake',target_is_directory=True)
run('pin-both-rehashed',q,d)
(R/'mutation-results-v3.json').write_text(json.dumps(results,indent=2)+'\n')
