"""State-publication primitive only: local transactions, no robot/certificate executor."""
import copy
import json
import sqlite3
import tempfile
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
from pathlib import Path
from threading import Barrier

P=Path(__file__).resolve().parent
BASE={'events':[['11/50','1/50']],'offset':'0','width':'1/5','version':0,'task':{'goal':'0','deadline':'17/10','version':0},'frame':'world-v1','calibration':'cal-v1','clock_domain':'exec-1','clock_epoch':1,'owner_epoch':1}

def encode(x):
    return json.dumps(x,sort_keys=True,separators=(',',':'))

def setup(path):
    with sqlite3.connect(path) as c:
        c.execute('CREATE TABLE live (id INTEGER PRIMARY KEY CHECK(id=1), body TEXT NOT NULL)')
        c.execute('CREATE TABLE outbox (event_id TEXT PRIMARY KEY, body TEXT NOT NULL)')
        c.execute('INSERT INTO live VALUES (1,?)',(encode(BASE),))

def state(path):
    with sqlite3.connect(path) as c:
        return c.execute('SELECT body FROM live').fetchone()[0],c.execute('SELECT count(*) FROM outbox').fetchone()[0]

def publish(path,expected,event_id,read_clock,*,fault=False,barrier=None):
    if barrier is not None:barrier.wait()
    c=sqlite3.connect(path,timeout=10,isolation_level=None)
    try:
        c.execute('BEGIN IMMEDIATE')
        current=c.execute('SELECT body FROM live WHERE id=1').fetchone()[0]
        if current!=expected:
            c.execute('ROLLBACK');return 'stale'
        # This callback supplies an interval for a model clock AFTER lock acquisition.
        # The publication-tail bound is a stated premise, not established by SQLite.
        now_upper=read_clock()
        publication_tail=F(1,100);dispatch_max=F(1,50);execution_lower=F(3,5)
        if now_upper+publication_tail+dispatch_max>execution_lower:
            c.execute('ROLLBACK');return 'expired'
        next_state=json.loads(current)
        next_state['events'].append(['31/50','-1/50'])
        next_state['version']+=1
        c.execute('UPDATE live SET body=? WHERE id=1',(encode(next_state),))
        if fault:raise RuntimeError('injected before outbox insert')
        c.execute('INSERT INTO outbox VALUES (?,?)',(event_id,encode({'execution':'31/50','delta':'-1/50','expected':expected})))
        c.execute('COMMIT');return 'published'
    except BaseException:
        if c.in_transaction:c.execute('ROLLBACK')
        raise
    finally:c.close()

def mutate(path,field,value):
    with sqlite3.connect(path) as c:
        x=json.loads(c.execute('SELECT body FROM live').fetchone()[0]);x[field]=value
        c.execute('UPDATE live SET body=?',(encode(x),))

results=[]
with tempfile.TemporaryDirectory(prefix='crossover-r03-') as td:
    root=Path(td)
    for k in range(32):
        path=root/f'race{k}.db';setup(path);barrier=Barrier(2)
        with ThreadPoolExecutor(max_workers=2) as pool:
            fs=[pool.submit(publish,path,encode(BASE),f'event{i}',lambda:F(1,2),barrier=barrier) for i in range(2)]
            rs=sorted(f.result() for f in fs)
        assert rs==['published','stale']
        body,count=state(path);x=json.loads(body)
        assert x['version']==1 and len(x['events'])==2 and count==1
        assert publish(path,encode(BASE),'retry',lambda:F(1,2))=='stale'
        results.append(rs)
    mutation_cases={
        'history':('events',[['11/50','2/50']]),'offset':('offset','1/1000'),
        'width':('width','1/4'),'frame':('frame','world-v2'),
        'calibration':('calibration','cal-v2'),'clock_domain':('clock_domain','exec-2'),
        'clock_epoch':('clock_epoch',2),'owner_epoch':('owner_epoch',2),
        'task':('task',{'goal':'1','deadline':'17/10','version':0}),
    }
    for name,(field,value) in mutation_cases.items():
        path=root/f'{name}.db';setup(path);mutate(path,field,value);old=state(path)
        assert publish(path,encode(BASE),name,lambda:F(1,2))=='stale' and state(path)==old
    path=root/'rollback.db';setup(path);old=state(path)
    try:publish(path,encode(BASE),'fault',lambda:F(1,2),fault=True)
    except RuntimeError:pass
    else:raise AssertionError('fault not exercised')
    assert state(path)==old
    path=root/'late.db';setup(path);old=state(path)
    assert publish(path,encode(BASE),'late',lambda:F(7,10))=='expired' and state(path)==old
    # Deliberate wrong callback returns old interval: database atomicity does not repair it.
    assert publish(path,encode(BASE),'stale-clock',lambda:F(1,2))=='published'
    stale_clock_counter={'cached_upper':'1/2','true_publication_time':'7/10','earliest_execution':'3/5','published':True,'physical_ordering':False}
    # Acknowledgement loss is outside a transaction over database rows.
    outbox_external_trace=['database commit','external effect','acknowledgement lost','replay outbox','external effect again']
    assert outbox_external_trace.count('external effect')+outbox_external_trace.count('external effect again')==2
out={'sqlite_version':sqlite3.sqlite_version,'concurrent_two_writer_rounds':len(results),'each_round':['published','stale'],'full_snapshot_mutations_rejected':list(mutation_cases),'fault_rollback_preserves_both':True,'fresh_late_clock_rejected':True,'stale_callback_counterexample':stale_clock_counter,'external_ack_loss_trace':outbox_external_trace,'scope':'Real local SQLite transactions test atomic snapshot+append+outbox state publication. Synthetic certificate fixture and model clock; no verified source certificate checker, bounded OS/fsync tail, physical event-time mapping, actual dispatch exactly-once, hard real-time or robot validation. Epochs trusted distinct/unbounded in model; no reset/wrap guarantee.'}
(P/'critic_sqlite_replay.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
