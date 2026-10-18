from pathlib import Path
import subprocess,sys,json,concurrent.futures
HERE=Path(__file__).resolve().parent
names=['late','stale-history','superseded-task','duplicate-result','tight-deadline']
def run(name):
    out=HERE/'client-results'/name
    args=[sys.executable,str(HERE/'client.py'),str(HERE/'clients'/(name+'.json')),str(out)]
    p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (HERE/('client-'+name+'.log')).write_text(p.stdout)
    row={'name':name,'returncode':p.returncode}
    if p.returncode==0:
        row['result']=json.loads((out/'result.json').read_text())
        assert row['result']['decision'] is False
    return row
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    rows=list(pool.map(run,names))
(HERE/'remaining-client-results.json').write_text(json.dumps({'status':'PASS' if all(r['returncode']==0 for r in rows) else 'FAIL','cases':rows},indent=2)+'\n')
print(json.dumps({'cases':len(rows),'exit_codes':[r['returncode'] for r in rows]}))
if any(r['returncode']!=0 for r in rows):sys.exit(1)
