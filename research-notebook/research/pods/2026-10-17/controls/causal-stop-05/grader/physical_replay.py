#!/usr/bin/env python3
"""Grader-authored 80-digit physical-state replay, without importing builder code.

The autonomous state includes actual plant state and all seven derivatives of
the degree-six reference. Only reference derivatives of order >=4 change at
joins. Matrix exponentials use mpmath Pade, not the root's Taylor cross-check.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial, ceil, floor
import csv, hashlib, json, time
import mpmath as mp

HERE=Path(__file__).resolve().parent
BUILDER=HERE.parent/'builder'
mp.mp.dps=80
DT=F(1,2000)
FIELDS=['q','qv','qa','j','snap','x','v','a','u','ustar','uprime','actual_jerk','ex','ev','ea']
def m(x):
    if isinstance(x,F): return mp.mpf(x.numerator)/x.denominator
    return mp.mpf(x)
def ev(p,t):
    result=F(0)
    for a in reversed(p): result=result*t+a
    return result
def der(p): return [i*p[i] for i in range(1,len(p))] or [F(0)]
def integ(p,c): return [c]+[x/(i+1) for i,x in enumerate(p)]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def encode(x):
    if isinstance(x,(mp.mpf,F)): return str(x)
    if isinstance(x,dict): return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [encode(v) for v in x]
    return x

# Independent construction from the accepted contract. Build by integration.
phases=[]; state=[F(0),F(0),F(0),F(10)]; t=F(0)
def add(name,duration,p):
    global state,t
    ds=[p]
    for _ in range(6): ds.append(der(ds[-1]))
    assert [ev(x,F(0)) for x in ds[:4]]==state
    phases.append({'name':name,'start':t,'end':t+duration,'polys':ds})
    state=[ev(x,duration) for x in ds[:4]];t+=duration
for name,duration,snap in [('old_plan',F(1,4),F(0)),('latency',F(1,200),F(0)),
    ('jerk_reversal',F(1,20),F(-400)),('negative_jerk_hold',F(97,400),F(0)),
    ('jerk_to_zero',F(1,40),F(400))]:
    p=[snap]
    for initial in reversed(state): p=integ(p,initial)
    add(name,duration,p)
V=state[1]; L=F(7,10)
assert state==[F(8782613,38400000),F(75089,96000),F(0),F(0)]
cruise=(F(3,5)-state[0]-V*L/2)/V
add('cruise',cruise,[state[0],V])
vpoly=[V,F(0),F(0),-10*V/L**3,15*V/L**4,-6*V/L**5]
add('brake',L,integ(vpoly,state[0]))
assert state==[F(3,5),F(0),F(0),F(0)] and t==F(10491307,7508900)
add('hold',F(3,2)-t,[F(3,5)])
stored_reference=json.loads((BUILDER/'reference.json').read_text())
for p,s in zip(phases,stored_reference):
    assert p['name']==s['name'] and p['start']==F(s['start']) and p['end']==F(s['end'])
    ps=p['polys'][0][:];ss=list(map(F,s['position_coefficients_local_time']))
    while len(ps)>1 and ps[-1]==0:ps.pop()
    while len(ss)>1 and ss[-1]==0:ss.pop()
    assert ps==ss
assert len(phases)==len(stored_reference)==8

def matrix(law,k):
    n=3 if law=='direct' else 4
    A=mp.zeros(n+8)
    A[0,1]=1; A[1,2]=1; A[2,n+7]=m(F(4,5))
    if law=='direct':
        for i,c in enumerate([-64000,-4800,-120]): A[2,i]=c
        for i,c in enumerate([F(64000),F(4800),F(120),80*k]): A[2,n+i]=m(c)
    else:
        A[2,2]=-80;A[2,3]=80
        for i,c in enumerate([-16000,-1200,-10,-20]): A[3,i]=c
        for i,c in enumerate([F(16000),F(1200),F(30),20*k]): A[3,n+i]=m(c)
    for i in range(6): A[n+i,n+i+1]=1
    return A,n

def output(y,n,law,k):
    x,v,a=y[0],y[1],y[2]
    q,qv,qa,j,snap=[y[n+i] for i in range(5)]
    ex,evv,ea=x-q,v-qv,a-qa
    us=qa-800*ex-60*evv-ea/2+m(k)*j
    u=us if law=='direct' else y[3]
    aj=80*(u+m(F(1,100))-a)
    up=3*j/2-800*evv-60*ea-aj/2+m(k)*snap if law=='direct' else 20*(us-u)
    return dict(zip(FIELDS,[q,qv,qa,j,snap,x,v,a,u,us,up,aj,ex,evv,ea]))

frozen=json.loads((HERE/'source-before.json').read_text())
assert {n:sha(BUILDER/n) for n in frozen['hashes']}==frozen['hashes']
summary=[]; started=time.monotonic()
for law,k in [('direct',F(1,96)),('filtered_original',F(1,96)),('filtered_compensated',F(29,480))]:
    rows=list(csv.DictReader((BUILDER/(law+'.csv')).open()))
    A,n=matrix(law,k); y=mp.zeros(n+8,1); y[n+3]=10; y[n+7]=1
    cache={}; differences={f:{'max_abs':mp.mpf(0)} for f in FIELDS}
    peaks={f:{'max_abs':mp.mpf(-1)} for f in ['ex','actual_jerk','u','ustar','uprime']}
    events=[]; prior=None; prior_t=None; count=0; tv=mp.mpf(0);travel=mp.mpf(0);tvtrap=mp.mpf(0)
    minx=mp.inf;maxx=-mp.inf;reference_residual=mp.mpf(0)
    with (HERE/(law+'-80digits.csv')).open('w') as file:
        writer=csv.DictWriter(file,fieldnames=['t_exact','phase','side']+FIELDS);writer.writeheader()
        for index,p in enumerate(phases):
            for i in range(4): assert abs(y[n+i]-m(ev(p['polys'][i],F(0))))<m('1e-65')
            # No plant or lower-reference-state reset.
            for i in range(4,7): y[n+i]=m(ev(p['polys'][i],F(0)))
            times=sorted({p['start'],p['end']}|{i*DT for i in range(ceil(p['start']/DT),floor(p['end']/DT)+1)})
            prev=p['start']
            for local_index,t in enumerate(times):
                delta=t-prev
                if delta:
                    if delta not in cache: cache[delta]=mp.expm(A*m(delta),method='pade')
                    y=cache[delta]*y
                side='start' if local_index==0 else ('end' if local_index==len(times)-1 else 'grid')
                old=rows[count]
                assert old['t_exact']==str(t) and int(old['phase'])==index and old['phase_name']==p['name'] and old['side']==side
                val=output(y,n,law,k)
                for i,f in enumerate(['q','qv','qa','j','snap']):
                    reference_residual=max(reference_residual,abs(val[f]-m(ev(p['polys'][i],t-p['start']))))
                for f in FIELDS:
                    diff=abs(val[f]-m(old[f]))
                    if diff>differences[f]['max_abs']:
                        differences[f]={'max_abs':diff,'t_exact':str(t),'side':side,'phase':index}
                    assert diff<m('2e-10'),(law,t,f,diff)
                for f in peaks:
                    if abs(val[f])>peaks[f]['max_abs']:
                        peaks[f]={'max_abs':abs(val[f]),'signed_value':val[f],'t_exact':str(t),'side':side,'phase':index}
                if prior is not None:
                    tv+=abs(val['u']-prior['u']);travel+=abs(val['x']-prior['x'])
                    tvtrap+=m(t-prior_t)*(abs(val['uprime'])+abs(prior['uprime']))/2
                    if side=='start':
                        continuous=['q','qv','qa','j','x','v','a','u','ustar','actual_jerk']
                        residual={f:val[f]-prior[f] for f in continuous}
                        assert max(abs(x) for x in residual.values())<m('1e-65')
                        expected_jump=m(k)*(val['snap']-prior['snap']) if law=='direct' else mp.mpf(0)
                        assert abs((val['uprime']-prior['uprime'])-expected_jump)<m('1e-65')
                        events.append({'t_exact':str(t),'continuous_residuals':residual,'uprime_jump':val['uprime']-prior['uprime'],'uprime_expected_jump':expected_jump})
                else:
                    initial=val.copy()
                    assert all(val[f]==0 for f in ['x','v','a'])
                    assert abs(val['u']-m(F(5,48) if law=='direct' else F(0)))<m('1e-70')
                    assert abs(val['actual_jerk']-m(F(137,15) if law=='direct' else F(4,5)))<m('1e-70')
                minx=min(minx,val['x']);maxx=max(maxx,val['x'])
                writer.writerow(encode({'t_exact':str(t),'phase':index,'side':side,**val}))
                prior=val;prior_t=t;prev=t;count+=1
    assert count==len(rows)==3010 and len(events)==7
    assert reference_residual<m('1e-65')
    result={'law':law,'rows_checked':count,'precision_digits':80,'method':'Physical plant plus seven reference derivative states; independent mpmath Pade exponential',
        'peak_checks':peaks,'max_difference_by_field':differences,'reference_polynomial_residual':reference_residual,
        'initial':initial,'endpoint':prior,'min_x':minx,'max_x':maxx,
        'sampled_command_total_variation':tv,'sampled_travel':travel,'trapezoid_integral_abs_uprime':tvtrap,
        'sampled_internal_position_pass':peaks['ex']['max_abs']<=m(F(1,5000)),
        'endpoint_position_pass':abs(prior['x']-m(F(3,5)))<=m(F(1,5000)),
        'events':events,'max_abs_comparison_error':max(x['max_abs'] for x in differences.values())}
    summary.append(result)
    print(json.dumps(encode({'law':law,'rows':count,'position_peak_mm':1000*peaks['ex']['max_abs'],'max_column_difference':result['max_abs_comparison_error']})),flush=True)
after={n:sha(BUILDER/n) for n in frozen['hashes']};assert after==frozen['hashes']
report={'passed':True,'rows_checked':sum(c['rows_checked'] for c in summary),'cases':summary,
    'builder_hashes_after':after,'builder_sources_stable':True,'reference_reconstructed_independently':True,
    'mpmath_version':mp.__version__,'elapsed_seconds':time.monotonic()-started,
    'scope':'All saved sample rows independently checked. No interval enclosure, new cases, gain tuning, physical-stop or corridor acceptance.'}
(HERE/'physical-replay.json').write_text(json.dumps(encode(report),indent=2)+'\n')
print(json.dumps({'passed':True,'rows':report['rows_checked'],'elapsed_seconds':report['elapsed_seconds']}),flush=True)
