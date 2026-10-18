#!/usr/bin/env python3
"""Independent input/scheduler/native reconstruction. Fixed native limits remain
unchanged. Failure is recorded per stream and never converted to a full-gate pass.
"""
from pathlib import Path
from fractions import Fraction as Q
from random import Random
from math import factorial,ceil,nextafter,inf,comb
from bisect import bisect_right
import hashlib,json,subprocess,sys,gzip
H=Path(__file__).resolve().parent;B=H.parent/'builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(n):return json.loads((B/n).read_text())
def dump(n,o):(H/n).write_text(json.dumps(o,indent=2)+'\n')
assert len(sys.argv)==2
manifest=load('artifact-sha256.json');assert sha(B/'artifact-sha256.json')==sys.argv[1]
assert all(sha(B/n)==v for n,v in manifest['files'].items())
for file in ['pre-run-input-manifest.json','pre-run-implementation-manifest.json']:
    assert all(sha(B/n)==v for n,v in load(file)['files'].items())
old=B.parents[1]/'comparison-04/builder';old_manifest=json.loads((old/'artifact-sha256.json').read_text())
assert sha(old/'artifact-sha256.json')=='f7c95b27384427f2cd48dcc4fabb7de7c5f33d6c37cbc61df73728095a898eef'
assert all(sha(old/n)==v for n,v in old_manifest['files'].items())
spec=load('packets.json');cases={c['id']:c for c in spec['cases']}
original=json.loads((old/'frozen-fixed-streams.json').read_text())
for name in ['hold_jitter','persistent_goal']:assert cases[name]==next(c for c in original['cases'] if c['id']==name)
assert len(cases)==6
# Reconstruct all added values and observation times from the contract.
rng=Random(20261017)
expected_values={
 'sign_60ms':[Q((-1)**i,1000) for i in range(20)]+[Q(0)],
 'irregular_alternation':[Q((-1)**i,1000) for i in range(20)]+[Q(0)],
 'seeded_random':[Q(rng.randint(-1000,1000),1000000) for i in range(80)]+[Q(0)],
 'biased_alternation':[Q(1,2500)+Q(3*(-1)**i,5000) for i in range(80)]+[Q(0)]}
gaps=[Q(x,100) for x in [2,6,4,8,2,10,6,4,2,8]]*2
irregular_times=[Q(1,5)]
for gap in gaps:irregular_times.append(irregular_times[-1]+gap)
expected_times={'sign_60ms':[Q(1,5)+i*Q(3,50) for i in range(21)],'irregular_alternation':irregular_times,
 'seeded_random':[Q(1,5)+i*Q(1,50) for i in range(81)],'biased_alternation':[Q(1,5)+i*Q(1,50) for i in range(81)]}
for name,values in expected_values.items():
    ps=cases[name]['packets'];assert [Q(p['target_m']) for p in ps]==values
    assert [Q(p['observed_s']) for p in ps]==expected_times[name]
    assert [Q(p['ready_s']) for p in ps]==[t+Q(1,50) for t in expected_times[name]]
    assert [p['sequence'] for p in ps]==list(range(100,100+len(ps)))
checks={x['case']:x for x in load('admission-transcripts.json')['cases']}
schedules={(s['case'],s['method']):s for s in load('reference-schedules.json')['schedules']};assert len(schedules)==24
h=Q(spec['h_s']);tick=Q(spec['commit_tick_s']);J=Q(15,2);coeff=[1,-4,6,-4,1]
def value(events,t,order):return sum((d*c*max(Q(0),t-tau-i*h)**(4-order)/factorial(4-order)/h**4 for tau,d in events for i,c in enumerate(coeff)),Q(0))
def peak(events,now):
    times=sorted({now}|{tau+i*h for tau,d in events for i in range(5) if tau+i*h>=now});pairs=[(abs(value(events,t,3)),t) for t in times];top=max(a for a,t in pairs)
    return top,next(t for a,t in pairs if a==top),len(times)
result={'status':'running','manifest_before':sys.argv[1],'input_reconstruction_passed':True,'cases':[],'native_exports':{},'native_clock':{},'smokes':{},'tiny_executed_phases':[],'native_state_limits':[1e-8,1e-8,1e-10]}
recovered={};replan_lists={}
for name,case in cases.items():
    groups={};seen={}
    for p in case['packets']:
        assert Q(p['ready_s'])>=Q(p['observed_s']);assert p['sequence'] not in seen or seen[p['sequence']]==p;seen[p['sequence']]=p
        c=ceil(Q(p['ready_s'])/tick)*tick;groups.setdefault(c,[]).append(p)
    events=[];ung=[];replans=[];wm=-1;goal=Q(0);ugoal=Q(0);outcomes=[];prefix=[]
    for c,packets in sorted(groups.items()):
        winner=max(packets,key=lambda p:p['sequence'])
        for p in sorted(packets,key=lambda p:p['sequence']):
            out={'sequence':p['sequence'],'commit_s':str(c)}
            if p is not winner:out['outcome']='coalesced_by_larger_sequence'
            elif p['sequence']<=wm:out['outcome']='stale_discard'
            else:
                wm=p['sequence'];target=Q(p['target_m']);delta=target-goal;candidate=events+([(c,delta)] if delta else [])
                maxj,tj,n=peak(candidate,c);out.update(delta_m=str(delta),future_reference_jerk_peak_m_s3=str(maxj),peak_time_s=str(tj),checked_future_knots=n)
                ud=target-ugoal
                if ud:ung.append((c,ud))
                ugoal=target
                if maxj>J:out['outcome']='jerk_rejected'
                else:out['outcome']='accepted';events=candidate;goal=target;replans.append((c,delta))
                prefix.append(events==ung)
            outcomes.append(out)
    stored=checks[name];assert len(outcomes)==len(stored['outcomes'])
    for a,b in zip(outcomes,stored['outcomes']):
        for k,v in a.items():assert v==b[k],(name,k,v,b[k])
    assert events==[(Q(t),Q(d)) for t,d in stored['accepted_events']];assert goal==Q(stored['final_accepted_goal_m'])
    recovered[name]=events;replan_lists[name]=replans
    entry={'case':name,'proposal_count':len(outcomes),'accepted_count':sum(o['outcome']=='accepted' for o in outcomes),'nonzero_events':len(events),'all_guarded_unguarded_prefixes_equal':all(prefix),'prefix_count':len(prefix)}
    assert all(prefix)
    if name!='persistent_goal':
        ps=case['packets'];interval=Q(ps[-1]['ready_s'])-Q(ps[0]['ready_s']);area=sum((Q(a['target_m'])*(Q(b['ready_s'])-Q(a['ready_s'])) for a,b in zip(ps,ps[1:])),Q(0))
        entry.update(sample_mean_m=str(sum((Q(p['target_m']) for p in ps[:-1]),Q(0))/len(ps[:-1])),time_weighted_mean_m=str(area/interval),noise_episode_duration_s=str(interval))
    for method in ['raw','fir','ruckig','ruckig_min_08']:
        s=schedules[name,method];assert s['admissions']==stored['outcomes'];assert s['hold_required']==(name!='persistent_goal')
        assert s['deadline_exact']==case['deadline_s'] and Q(s['horizon_exact'])==Q(case['end_s'])
        assert [(Q(z['time_exact']),z['position']) for z in s['truth']]==[(Q(z['time_s']),float(Q(z['position_m']))) for z in case['truth']]
        required={Q(0),Q(case['end_s']),Q(case['deadline_s'])}|{Q(z['time_s']) for z in case['truth']}|{Q(p[k]) for p in case['packets'] for k in ['observed_s','ready_s']}|set(groups)
        assert required <= {Q(e['time_exact']) for e in s['common_events']}
    bounds={k:Q(0) for k in [1,2,3]}
    for method in ['raw','fir']:
        for p in schedules[name,method]['pieces']:
            t=Q(p['start_exact']);end=Q(p['end_exact']);mid=(t+end)/2
            if method=='raw':ds=[sum((d for tau,d in events if tau<=t),Q(0)),Q(0),Q(0),Q(0),Q(0)]
            else:
                ds=[sum((d*c*(t-tau-i*h)**(4-k)/factorial(4-k)/h**4 for tau,d in events for i,c in enumerate(coeff) if tau+i*h<mid),Q(0)) for k in range(5)]
                assert [str(x) for x in ds]==p['rational_derivatives_at_start']
                for order in [1,2,3]:
                    power=[ds[order+i]*(end-t)**i/factorial(i) for i in range(5-order)];n=len(power)-1
                    bs=[sum(power[i]*Q(comb(k,i),comb(n,i)) for i in range(k+1)) for k in range(n+1)]
                    bounds[order]=max(bounds[order],*map(abs,bs))
            assert [float(x) for x in ds]==[p[k] for k in ['p','v','a','jerk','snap']]
    assert all(bounds[k]<=v for k,v in {1:Q(1,10),2:Q(1,2),3:J}.items())
    entry['FIR_exact_Bernstein_bounds']={str(k):str(v) for k,v in bounds.items()};result['cases'].append(entry)
provenance=load('ruckig-provenance.json');cache=B/'.cache';native=cache/'native_replay';exporter=cache/'ruckig_export'
assert sha(native)==provenance['native_replay_executable_sha256'] and sha(exporter)==provenance['executable_sha256']
assert provenance['revision']=='99751e6ebc7c963bb80e99fbbe66f2c279d1db57' and not provenance['cloud_enabled']
source=cache/('ruckig-'+provenance['revision']);assert all(sha(source/n)==s for n,s in provenance['source_tree_sha256'].items())
exports=load('ruckig-primary-exports.json')
def strip(o):
    if isinstance(o,list):return [strip(x) for x in o]
    if isinstance(o,dict):return {k:strip(v) for k,v in o.items() if k not in ['input','time_representation','binary_time_metadata']}
    return o

def ref_at(s,t):
    pieces=s['pieces'];starts=[Q(p['start_exact']) for p in pieces];i=max(0,min(bisect_right(starts,t)-1,len(pieces)-1));p=pieces[i];z=t-Q(p['start_exact']);d=[Q(p[k]) for k in ['p','v','a','jerk','snap']]
    return [float(sum(d[i]*z**(i-k)/factorial(i-k) for i in range(k,5))) for k in range(4)]
for name,case in cases.items():
 for method,minimum in [('ruckig',0.),('ruckig_min_08',.8)]:
    key=name+'__'+method;plans=exports[key];replans=replan_lists[name];assert len(plans)==len(replans)
    state=[0.,0.,0.];target=Q(0);rebuilt=[];commits=[]
    if replans[0][0]>0:rebuilt.append((Q(0),replans[0][0],[0.,0.,0.,0.,0.],'initial_rest'))
    for k,((tau,delta),stored) in enumerate(zip(replans,plans)):
        stop=replans[k+1][0] if k+1<len(replans) else Q(case['end_s']);target+=delta;elapsed=float(stop-tau)
        assert Q(stored['commit_rational'])==tau and Q(stored['executed_until_rational'])==stop
        assert stored['plan']['input']=={'state':state,'target':float(target),'queries':[elapsed],'minimum_duration':minimum}
        args=[str(exporter)]+[format(float(x),'.17g') for x in [*state,target,minimum,elapsed]]
        fresh=json.loads(subprocess.check_output(args,text=True));assert fresh==strip(stored['plan']),(key,k)
        assert fresh['duration']>=minimum and fresh['accel_duration']==0
        commits.append((float(tau),float(target)))
        for p in fresh['phases']:
            original=next(q for q in stored['plan']['phases'] if q['kind']==p['kind'] and q.get('index')==p.get('index'))
            for field,meta in original['binary_time_metadata'].items():assert Q(meta['ratio'])==Q(p[field]) and float.fromhex(meta['hex'])==p[field]
            if p['duration']<=0 or p['start']>=elapsed:continue
            left=tau+Q(p['start']);right=min(stop,tau+Q(p['end']));assert right>left
            rebuilt.append((left,right,[p[n] for n in ['p','v','a','jerk']]+[0.],f'plan_{k}_{p["kind"]}_{p["index"]}'))
            if right-left<Q(1,10**12):result['tiny_executed_phases'].append({'key':key,'plan':k,'start':str(left),'end':str(right),'duration':str(right-left),'float_clock_collapses':float(left)==float(right)})
        if fresh['duration']<elapsed:
            p=fresh['tail'];rebuilt.append((tau+Q(p['start']),stop,[p[n] for n in ['p','v','a','jerk']]+[0.],f'plan_{k}_extrapolated_tail'))
        row=next(r for r in fresh['samples'] if r['t']==elapsed);state=[row[n] for n in ['p','v','a']]
    schedule=schedules[name,method];assert len(schedule['pieces'])==len(rebuilt)
    for a,b in zip(schedule['pieces'],rebuilt):
        assert Q(a['start_exact'])==b[0] and Q(a['end_exact'])==b[1] and a['origin']==b[3]
        assert [a[k] for k in ['p','v','a','jerk','snap']]==b[2]
    result['native_exports'][key]={'reproduced_plans':len(plans),'reproduced_pieces':len(rebuilt)}
    times={float(Q(k,2000)) for k in range(int(Q(case['end_s'])*2000)+1)}
    for p in schedule['pieces']:
        for field in ['start_exact','end_exact']:
            t=float(Q(p[field]));times.add(t)
            if t>0:times.add(nextafter(t,0.));times.add(nextafter(t,inf))
    times=sorted(t for t in times if 0<=t<=float(Q(case['end_s'])))
    text=str(len(commits))+'\n'+'\n'.join(format(t,'.17g')+' '+format(g,'.17g') for t,g in commits)+'\n'+str(len(times))+'\n'+'\n'.join(format(t,'.17g') for t in times)+'\n'
    (H/('native-'+key+'-input.txt')).write_text(text)
    out=subprocess.check_output([str(native),format(minimum,'.17g')],input=text,text=True)
    with (H/('native-'+key+'-output.json.gz')).open('wb') as f:
        with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:z.write(out.encode())
    data=json.loads(out);assert len(data['commits'])==len(plans) and len(data['queries'])==len(times)
    assert [(r['time'],r['target']) for r in data['commits']]==commits
    assert [r['time'] for r in data['queries']]==times
    maxima=[0.]*3;worst=[None]*3;branches=[];commitmax=[0.]*3;commit_worst=[None]*3
    boundaries=[Q(p['start_exact']) for p in schedule['pieces']]+[Q(schedule['horizon_exact'])]
    for row in data['queries']:
        t=Q(row['time']);q=ref_at(schedule,t)
        for i,field in enumerate(['q','qv','qa']):
            d=abs(row[field]-q[i])
            if d>maxima[i]:maxima[i]=d;worst[i]={'time':row['time'],'native':row[field],'canonical':q[i],'difference':d,'distance_to_boundary_s':float(min(abs(t-b) for b in boundaries))}
        if row['jerk']!=q[3]:branches.append({'time':row['time'],'native_jerk':row['jerk'],'canonical_jerk':q[3],'nearest_boundary_distance_s':float(min(abs(t-b) for b in boundaries))})
    for index,(row,p) in enumerate(zip(data['commits'],plans)):
        for i,field in enumerate(['current_p','current_v','current_a']):
            d=abs(row[field]-p['plan']['input']['state'][i])
            if d>commitmax[i]:commitmax[i]=d;commit_worst[i]={'plan_index':index,'time':row['time'],'native':row[field],'canonical':p['plan']['input']['state'][i],'difference':d}
    passed=all(d<=tol for d,tol in zip(maxima,result['native_state_limits']))
    result['native_clock'][key]={'passed_fixed_state_limits':passed,'query_count':len(times),'commit_count':len(plans),'max_q_v_a_disagreement':maxima,'worst_q_v_a':worst,'max_commit_q_v_a_disagreement':commitmax,'worst_commit_q_v_a':commit_worst,'jerk_branch_differences':branches}
    dump('schedule-review.json',result);print(key,'native fixed gate',passed,'max',maxima,flush=True)
# Verify both ordinary and minimum-duration pre-run smoke exports.
for filename in ['ruckig-smoke-exports.json','duration-smoke-exports.json']:
 for name,stored in load(filename).items():
    inp=stored['input'];args=[str(exporter)]+[format(float(x),'.17g') for x in [*inp['state'],inp['target'],inp['minimum_duration'],*inp['queries']]]
    fresh=json.loads(subprocess.check_output(args,text=True));assert fresh==strip(stored)
    positive=[p for p in fresh['phases'] if p['duration']>0];maxres=[0.]*3
    for row in fresh['samples']:
        t=row['t'];p=fresh['tail'] if t>=fresh['duration'] else next(p for p in reversed(positive) if p['start']<=t)
        z=Q(t)-Q(p['start']);d=[Q(p[k]) for k in ['p','v','a','jerk']]
        q=[float(sum(d[i]*z**(i-k)/factorial(i-k) for i in range(k,4))) for k in range(3)]
        for i,field in enumerate(['p','v','a']):maxres[i]=max(maxres[i],abs(row[field]-q[i]))
    passed=all(d<=tol for d,tol in zip(maxres,result['native_state_limits']));assert passed
    result['smokes'][filename+':'+name]={'passed':passed,'max_q_v_a':maxres,'duration':fresh['duration'],'minimum_duration':fresh['minimum_duration']}
result['all_artifacts_unchanged']=all(sha(B/n)==v for n,v in manifest['files'].items()) and sha(B/'artifact-sha256.json')==sys.argv[1]
result['comparison04_unchanged']=all(sha(old/n)==v for n,v in old_manifest['files'].items())
result['canonical_schedule_passed']=result['all_artifacts_unchanged'] and result['comparison04_unchanged']
result['strict_native_gate_passed']=all(x['passed_fixed_state_limits'] for x in result['native_clock'].values())
result['failed_native_streams']=[k for k,v in result['native_clock'].items() if not v['passed_fixed_state_limits']]
result['status']='complete';dump('schedule-review.json',result)
print(json.dumps({k:result[k] for k in ['canonical_schedule_passed','strict_native_gate_passed','failed_native_streams','all_artifacts_unchanged','comparison04_unchanged']}))
