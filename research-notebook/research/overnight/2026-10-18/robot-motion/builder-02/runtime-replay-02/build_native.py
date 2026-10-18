"""Compile only local frontends against the verified pinned05 static library."""
from pathlib import Path
import hashlib,json,platform,subprocess
HERE=Path(__file__).resolve().parent
OLD=HERE.parents[4]/'research/pods/2026-10-17/robot-motion/latency-noise-05/builder'
PIN='99751e6ebc7c963bb80e99fbbe66f2c279d1db57'
CACHE=HERE/'.cache';CACHE.mkdir(exist_ok=True)
SOURCE=OLD/'.cache'/('ruckig-'+PIN)
LIBRARY=OLD/'.cache/build/libruckig.a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prior=json.loads((OLD/'ruckig-provenance.json').read_text())
assert prior['revision']==PIN and not prior['cloud_enabled']
assert sha(LIBRARY)==prior['library_sha256']
for name,digest in prior['source_tree_sha256'].items():assert sha(SOURCE/name)==digest,name
logs=[]
for stem in ['native_execution','native_replay']:
    command=['clang++','-std=c++20','-O2','-I'+str(SOURCE/'include'),str(HERE/(stem+'.cpp')),str(LIBRARY),'-o',str(CACHE/stem)]
    result=subprocess.run(command,text=True,capture_output=True)
    logs.append({'command':command,'returncode':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
    (HERE/'build-log.json').write_text(json.dumps(logs,indent=2)+'\n')
    result.check_returncode()
result={'revision':PIN,'repository':prior['repository'],'library_path':str(LIBRARY),'library_sha256':sha(LIBRARY),
        'prior_provenance_sha256':sha(OLD/'ruckig-provenance.json'),'source_tree_hashes_verified':len(prior['source_tree_sha256']),
        'source_and_library_reused_without_modification':True,'cloud_enabled':False,'local_library_patches':[],
        'compiler':subprocess.check_output(['clang++','--version'],text=True),'platform':platform.platform(),
        'commands':[x['command'] for x in logs],
        'sources':{n:sha(HERE/n) for n in ['native_execution.cpp','profile_export.hpp','native_replay.cpp']},
        'executables':{n:sha(CACHE/n) for n in ['native_execution','native_replay']},'license_sha256':sha(HERE/'RUCKIG-LICENSE')}
(HERE/'native-build-provenance.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
