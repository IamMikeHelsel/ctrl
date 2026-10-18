from pathlib import Path
import os,json,subprocess,re,time
B=Path(__file__).resolve().parent; E=json.loads((B/'environment.json').read_text());T=B/'cache/review-01'
env=os.environ.copy()
for k in ['LEAN_PATH','ELAN_HOME','PATH']:env[k]=E[k]
steps=[]
def run(label,args):
    t=time.monotonic();p=subprocess.run(args,cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    (B/'logs'/(label+'.txt')).write_text(p.stdout)
    steps.append({'name':label,'returncode':p.returncode,'seconds':time.monotonic()-t,'command':args})
    print(label,p.returncode,flush=True);assert p.returncode==0,p.stdout
    return p.stdout
source=(B/'clients/CounterWitnesses.lean').read_text();(T/'CounterWitnesses.lean').write_text(source)
run('CounterWitnesses',[E['compiler'],'--root='+str(T),'-o',str(T/'CounterWitnesses.olean'),str(T/'CounterWitnesses.lean')])
run('kernel-CounterWitnesses',[str(Path(E['compiler']).with_name('leanchecker')),'CounterWitnesses','-v'])
audit=(B/'clients/Audit.lean').read_text().replace('import ReviewerClient','import CounterWitnesses').replace('`ReviewerClient]', '`ReviewerClient, `CounterWitnesses]')
(B/'clients/FinalAudit.lean').write_text(audit);(T/'FinalAudit.lean').write_text(audit)
out=run('FinalAudit',[E['compiler'],str(T/'FinalAudit.lean')]);rows=[s for s in out.splitlines() if s.startswith('AUDIT|')]
mods=E['module_order']+['ReviewerClient','CounterWitnesses']
counts={m:sum(row.startswith('AUDIT|'+m+'|') for row in rows) for m in mods}
assert all(counts.values()),counts
(B/'counter-result.json').write_text(json.dumps({'status':'PASS','proved_counter_witnesses':len(re.findall(r'^theorem ',source,re.M)),'audited_local_declarations':len(rows),'module_counts':counts,'steps':steps},indent=2)+'\n')
