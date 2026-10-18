from pathlib import Path
import sys,hashlib,json,subprocess,time,datetime
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import dev

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parent=HERE.parent
    original=json.loads((parent/'artifact-sha256.json').read_text())
    for n,v in original['files'].items():assert sha(parent/n)==v['sha256'],n
    env,lean,deps=dev.environment()
    deps=':'.join(x for x in deps.split(':') if Path(x).resolve() != (dev.BASE/'.lake/build/lib/lean').resolve())
    env['LEAN_PATH']=str(parent/'.cache/fresh')+':'+deps
    command=[lean,'--root='+str(HERE),str(HERE/'FalseNoSafeRejectedHistory.lean')]
    start=time.monotonic();p=subprocess.run(command,cwd=HERE,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=HERE/'negative.log';log.write_text(p.stdout)
    print(p.stdout)
    assert p.returncode!=0 and 'error:' in p.stdout and '⊢ False' in p.stdout
    assert not any(x in p.stdout for x in ['unknown identifier','unknown constant','object file','unknown module prefix','made no progress'])
    for n,v in original['files'].items():assert sha(parent/n)==v['sha256'],n
    result={'status':'PASS','meaning':'Corrected false claim reaches False; original tactic failure excluded.',
      'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':command,'exit_code':p.returncode,
      'seconds':time.monotonic()-start,'source_sha256':sha(HERE/'FalseNoSafeRejectedHistory.lean'),
      'log_sha256':sha(log),'original_manifest_sha256':sha(parent/'artifact-sha256.json'),
      'original_artifact_preservation':'PASS','frozen_source_rebuild':'Previously verified 15-module fresh cache reused; no proof source changed.'}
    (HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
