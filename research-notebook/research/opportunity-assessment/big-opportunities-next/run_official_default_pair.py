from pathlib import Path
import subprocess,os,time,json,signal,hashlib
B=Path(__file__).resolve().parent
root=B.parents[2]
env={**os.environ,"ELAN_HOME":str(root/'.tools/elan'),"PATH":str(root/'.tools/elan/bin')+':'+os.environ['PATH']}
spec=B/'lean-kernel/evaluation/problems/permanent/Spec.lean'
before=hashlib.sha256(spec.read_bytes()).hexdigest()
results={}
for name,source in [('baseline',B/'lean-kernel/problems/permanent/Submission.lean'),('sparse',B/'kernel-spike/Submission.lean')]:
    command=['python3','evaluation/run.py','--problem','permanent','--submission',str(source),'--timeout','120']
    t=time.monotonic()
    with (B/f'{name}-official-default-local.log').open('w') as f:
        p=subprocess.Popen(command,cwd=B/'lean-kernel',env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        try: code=p.wait(timeout=420)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGTERM)
            try:p.wait(timeout=5)
            except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
            code=124
    results[name]={'command':command,'exit_code':code,'wall_seconds':time.monotonic()-t,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    token=hashlib.sha256(str(source.resolve()).encode()).hexdigest()[:16]
    verdict=B/f'lean-kernel/results/local-evaluation/permanent/{token}.json'
    if verdict.exists():
        results[name]['verdict']=str(verdict.relative_to(B))
        (B/f'{name}-official-default-local.json').write_bytes(verdict.read_bytes())
    (B/'official-default-local-pair.json').write_text(json.dumps({'spec_sha256_before':before,'spec_sha256_after':hashlib.sha256(spec.read_bytes()).hexdigest(),'local_unseeded_public_plan_only':True,'results':results},indent=2)+'\n')
    print(name,code,results[name]['wall_seconds'],flush=True)
