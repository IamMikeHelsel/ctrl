from pathlib import Path
import hashlib,json,platform,shutil,subprocess,tarfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
PIN='99751e6ebc7c963bb80e99fbbe66f2c279d1db57'
CACHE=HERE/'.cache'
SOURCE=CACHE/('ruckig-'+PIN)
BUILD=CACHE/'build'
ARCHIVE=CACHE/(PIN+'.tar.gz')
URL='https://codeload.github.com/pantor/ruckig/tar.gz/'+PIN
CACHE.mkdir(exist_ok=True)
if not ARCHIVE.exists(): subprocess.run(['curl','--fail','--location','--silent','--show-error',URL,'--output',str(ARCHIVE)],check=True)
if not SOURCE.exists():
    with tarfile.open(ARCHIVE) as archive: archive.extractall(CACHE,filter='data')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
audit=json.loads((ROOT/'research/pods/2026-10-17/robot-motion/ultra-preflight-02/ruckig-source-audit.json').read_text())
assert audit['revision']==PIN
for item in audit['files']:assert sha(SOURCE/item['path'])==item['sha256'],item['path']
flags=['-DCMAKE_BUILD_TYPE=Release','-DBUILD_CLOUD_CLIENT=OFF','-DBUILD_SHARED_LIBS=OFF','-DBUILD_EXAMPLES=OFF','-DBUILD_TESTS=OFF','-DBUILD_PYTHON_MODULE=OFF','-DBUILD_BENCHMARK=OFF']
commands=[['cmake','-S',str(SOURCE),'-B',str(BUILD),*flags],['cmake','--build',str(BUILD),'--parallel','2'],['clang++','-std=c++20','-O2','-I'+str(SOURCE/'include'),str(HERE/'ruckig_export.cpp'),str(BUILD/'libruckig.a'),'-o',str(CACHE/'ruckig_export')]]
commands.append(['clang++','-std=c++20','-O2','-I'+str(SOURCE/'include'),str(HERE/'native_replay.cpp'),str(BUILD/'libruckig.a'),'-o',str(CACHE/'native_replay')])
logs=[]
for command in commands:
    result=subprocess.run(command,text=True,capture_output=True)
    logs.append({'command':command,'returncode':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
    (HERE/'build-log.json').write_text(json.dumps(logs,indent=2)+'\n')
    result.check_returncode()
shutil.copyfile(SOURCE/'LICENSE',HERE/'RUCKIG-LICENSE')
provenance={'repository':'https://github.com/pantor/ruckig','revision':PIN,'cmake_version':'0.19.6','online_documentation_version':'0.19.7','archive_url':URL,'archive_sha256':sha(ARCHIVE),'source_tree_sha256':{str(p.relative_to(SOURCE)):sha(p) for p in sorted(SOURCE.rglob('*')) if p.is_file()},'commands':commands,'compiler':subprocess.check_output(['clang++','--version'],text=True),'platform':platform.platform(),'exporter_source_sha256':sha(HERE/'ruckig_export.cpp'),'library_sha256':sha(BUILD/'libruckig.a'),'executable_sha256':sha(CACHE/'ruckig_export'),'license_sha256':sha(HERE/'RUCKIG-LICENSE'),'cloud_enabled':False,'local_patches':[]}
provenance['native_replay_source_sha256']=sha(HERE/'native_replay.cpp')
provenance['native_replay_executable_sha256']=sha(CACHE/'native_replay')
(HERE/'ruckig-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
print(json.dumps({k:v for k,v in provenance.items() if k in ['revision','archive_sha256','executable_sha256','cloud_enabled']},indent=2))
