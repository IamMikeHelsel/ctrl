from pathlib import Path
import datetime,hashlib,json,os,subprocess,shutil,time,threading
HERE=Path(__file__).resolve().parent;BUILDER=HERE.parent/'builder-05'
E=json.loads((HERE/'environment.json').read_text());FRESH=Path(E['fresh_root'])
env=os.environ.copy();env.update({k:E[k] for k in ['ELAN_HOME','LEAN_PATH','PATH']})
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,where,name):
    r=subprocess.run(args,cwd=where,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (HERE/'logs'/f'{name}.log').write_text(r.stdout)
    assert r.returncode==0,(name,r.stdout[-5000:]);return r.stdout

def main():
    result={'status':'RUNNING','clients':[]}
    dst=FRESH/'ReviewClients.lean';shutil.copyfile(HERE/'ReviewClients.lean',dst)
    run([E['lean'],'--root='+str(FRESH),'-o',str(dst.with_suffix('.olean')),str(dst)],FRESH,'review-clients')
    run([E['checker'],'ReviewClients','-v'],FRESH,'review-clients-kernel')
    result['independent_lean_clients']='PASS'
    for p in sorted((BUILDER/'clients').glob('*.json')):
        out=HERE/'json-clients'/p.stem
        run(['python3',str(BUILDER/'client.py'),str(p),str(out)],HERE,'json-'+p.stem)
        proof=out/'ClientProof.lean'
        fresh_client=FRESH/('JSON'+p.stem.replace('-','_')+'.lean')
        shutil.copyfile(proof,fresh_client)
        run([E['lean'],'--root='+str(FRESH),'-o',str(fresh_client.with_suffix('.olean')),str(fresh_client)],FRESH,'fresh-json-'+p.stem)
        run([E['checker'],fresh_client.stem,'-v'],FRESH,'fresh-json-kernel-'+p.stem)
        record=json.loads((out/'result.json').read_text());record['case']=p.stem;record['fresh_review_rebuild']=True
        result['clients'].append(record)
        (HERE/'client-review-result.json').write_text(json.dumps(result,indent=2)+'\n')
    # Actual wrapper run with a controlled concurrent input replacement. The
    # generated proof and kernel replay remain real; only its input path changes.
    test=HERE/'input-race';test.mkdir()
    before=(BUILDER/'clients/on-time.json').read_bytes();(test/'before.json').write_bytes(before)
    inp=test/'input.json';inp.write_bytes(before)
    after=json.loads(before);after['liveTask']['goal']='1/200'
    afterbytes=(json.dumps(after,indent=2)+'\n').encode();(test/'after.json').write_bytes(afterbytes)
    out=test/'output';changed=[]
    def replace():
        stop=time.monotonic()+90
        while time.monotonic()<stop:
            if (out/'ClientProbe.lean').exists():inp.write_bytes(afterbytes);changed.append(True);return
            time.sleep(.01)
        raise RuntimeError('probe did not appear')
    watcher=threading.Thread(target=replace);watcher.start()
    run(['python3',str(BUILDER/'client.py'),str(inp),str(out)],HERE,'input-race')
    watcher.join();assert changed
    r=json.loads((out/'result.json').read_text())
    assert r['decision'] and r['input_sha256']==sha(test/'after.json') and sha(test/'before.json')!=r['input_sha256']
    (test/'finding.json').write_text(json.dumps({'wrapper_provenance_defect_reproduced':True,'proved_original_input_sha256':sha(test/'before.json'),'reported_changed_input_sha256':r['input_sha256'],'actual_input_used':'before.json','proof_goal':'0','reported_input_live_goal':'1/200','theorem_unsoundness':False},indent=2)+'\n')
    result['input_hash_race']='REPRODUCED; wrapper provenance requires repair, theorem unaffected'
    result['status']='PASS WITH WRAPPER REPAIR';result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (HERE/'client-review-result.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
