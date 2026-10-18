from pathlib import Path
import hashlib,json,platform,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
OLD=ROOT/'research/pods/2026-10-17/robot-motion/latency-noise-05/builder'
PIN='99751e6ebc7c963bb80e99fbbe66f2c279d1db57'
CACHE=HERE/'.cache';CACHE.mkdir(exist_ok=True)
SOURCE=OLD/'.cache'/('ruckig-'+PIN);LIBRARY=OLD/'.cache/build/libruckig.a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prior=json.loads((OLD/'ruckig-provenance.json').read_text())
assert prior['revision']==PIN and not prior['cloud_enabled']
assert sha(LIBRARY)==prior['library_sha256']
for name,digest in prior['source_tree_sha256'].items():assert sha(SOURCE/name)==digest,name
logs=[]
for stem in ['native_suffix','native_queries']:
 command=['clang++','-std=c++20','-O2','-I'+str(SOURCE/'include'),str(HERE/(stem+'.cpp')),str(LIBRARY),'-o',str(CACHE/stem)]
 run=subprocess.run(command,text=True,capture_output=True);logs.append({'command':command,'returncode':run.returncode,'stdout':run.stdout,'stderr':run.stderr});(HERE/'native-build-log.json').write_text(json.dumps(logs,indent=2)+'\n');run.check_returncode()
result={'revision':PIN,'repository':prior['repository'],'library_path':str(LIBRARY),'library_sha256':sha(LIBRARY),'prior_provenance_path':str(OLD/'ruckig-provenance.json'),'prior_provenance_sha256':sha(OLD/'ruckig-provenance.json'),'source_tree_sha256':prior['source_tree_sha256'],'source_path':str(SOURCE),'source_and_library_reused_without_modification':True,'cloud_enabled':False,'local_library_patches':[],'compiler':subprocess.check_output(['clang++','--version'],text=True),'platform':platform.platform(),'sources':{n:sha(HERE/n) for n in ['native_suffix.cpp','native_queries.cpp','profile_export.hpp']},'executables':{n:sha(CACHE/n) for n in ['native_suffix','native_queries']},'license_sha256':sha(HERE/'RUCKIG-LICENSE')}
(HERE/'native-build-provenance.json').write_text(json.dumps(result,indent=2)+'\n')
