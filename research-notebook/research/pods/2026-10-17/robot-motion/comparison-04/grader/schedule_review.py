#!/usr/bin/env python3
"""Independent fixture, scheduler, reference, and pinned native replay checks."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,ceil,nextafter,inf
from bisect import bisect_right
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;B=HERE.parent/'builder'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(n):return json.loads((B/n).read_text())
def dump(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
manifest=load('artifact-sha256.json')
assert sha(B/'artifact-sha256.json')=='f7c95b27384427f2cd48dcc4fabb7de7c5f33d6c37cbc61df73728095a898eef'
assert all(sha(B/n)==v for n,v in manifest['files'].items())
spec=load('frozen-fixed-streams.json');checks={x['case']:x for x in load('frozen-reference-checks.json')['cases']}
schedules={(s['case'],s['method']):s for s in load('reference-schedules.json')['schedules']}
h=Q(spec['h_s']);tick=Q(spec['commit_tick_s']);J=Q(spec['reference_jerk_limit_m_s3']);coeff=[1,-4,6,-4,1]
def val(events,t,order):
    return sum((delta*c*max(Q(0),t-tau-i*h)**(4-order)/factorial(4-order)/h**4 for tau,delta in events for i,c in enumerate(coeff)),Q(0))
def future_peak(events,now):
    times=sorted({now}|{tau+i*h for tau,delta in events for i in range(5) if tau+i*h>=now})
    pairs=[(abs(val(events,t,3)),t) for t in times]
    peak=max(p[0] for p in pairs)
    return peak,next(t for a,t in pairs if a==peak),len(times)
result={'status':'running','fixture_manifest_sha256':sha(B/'artifact-sha256.json'),'cases':[],'native':{},'native_export_reproduction':{},'tiny_executed_phases':[]}
recovered={}
for case in spec['cases']:
    groups={};seen={}
    for p in case['packets']:
        assert Q(p['ready_s'])>=Q(p['observed_s'])
        assert p['sequence'] not in seen or seen[p['sequence']]==p
        seen[p['sequence']]=p
        commit=ceil(Q(p['ready_s'])/tick)*tick;groups.setdefault(commit,[]).append(p)
    events=[];watermark=-1;goal=Q(0);outcomes=[]
    for now,ps in sorted(groups.items()):
        winner=max(ps,key=lambda p:p['sequence'])
        for p in sorted(ps,key=lambda p:p['sequence']):
            record={'sequence':p['sequence'],'commit_s':str(now)}
            if p is not winner:record['outcome']='coalesced_by_larger_sequence'
            elif p['sequence']<=watermark:record['outcome']='stale_discard'
            else:
                watermark=p['sequence'];delta=Q(p['target_m'])-goal;candidate=events+([(now,delta)] if delta else [])
                peak,peak_time,count=future_peak(candidate,now)
                record.update(delta_m=str(delta),future_reference_jerk_peak_m_s3=str(peak),peak_time_s=str(peak_time),checked_future_knots=count)
                if peak>J:record['outcome']='jerk_rejected'
                else:
                    record['outcome']='accepted';events=candidate;goal=Q(p['target_m'])
            outcomes.append(record)
    frozen=checks[case['id']]
    assert len(outcomes)==len(frozen['outcomes'])
    for actual,expected in zip(outcomes,frozen['outcomes']):
        for k,v in actual.items():assert v==expected[k],(case['id'],k,v,expected[k])
    assert events==[(Q(e['time_s']),Q(e['delta_m'])) for e in frozen['accepted_events']]
    assert goal==Q(frozen['final_accepted_goal_m'])
    at_deadline=val(events,Q(case['deadline_s']),0)
    assert at_deadline==Q(frozen['reference_at_deadline_m'])
    recovered[case['id']]=events
    entry={'case':case['id'],'role':case['role'],'events':[(str(t),str(d)) for t,d in events],'outcomes':outcomes,'deadline_reference':str(at_deadline),'final_accepted_goal':str(goal)}
    if case['role']=='primary':
        for method in ['raw','fir','ruckig']:
            schedule=schedules[case['id'],method];assert schedule['admissions']==frozen['outcomes']
            assert schedule['deadline_exact']==case['deadline_s'] and Q(schedule['horizon_exact'])==Q(case['end_s'])
        for method in ['raw','fir']:
            for p in schedules[case['id'],method]['pieces']:
                t=Q(p['start_exact']);end=Q(p['end_exact']);mid=(t+end)/2
                if method=='raw':ds=[sum((d for tau,d in events if tau<=t),Q(0)),Q(0),Q(0),Q(0),Q(0)]
                else:
                    # Piece's fourth derivative chooses the interior branch at the start.
                    ds=[sum((d*c*(t-tau-i*h)**(4-k)/factorial(4-k)/h**4 for tau,d in events for i,c in enumerate(coeff) if tau+i*h<mid),Q(0)) for k in range(5)]
                    assert [str(x) for x in ds]==p['rational_derivatives_at_start']
                assert [float(x) for x in ds]==[p[k] for k in ['p','v','a','jerk','snap']]
        entry['raw_and_fir_schedule_coefficients_match']=True
    result['cases'].append(entry)
assert len(schedules)==12
negative=load('retained-negative-cases.json')['cases'];assert negative==[checks[c['id']] for c in spec['cases'] if c['role']!='primary']
result['retained_negative_and_semantic_cases_match']=True
provenance=load('ruckig-provenance.json');cache=B/'.cache';native=cache/'native_replay';exporter=cache/'ruckig_export'
assert sha(native)==provenance['native_replay_executable_sha256']
assert sha(exporter)==provenance['executable_sha256']
assert provenance['revision']=='99751e6ebc7c963bb80e99fbbe66f2c279d1db57' and provenance['cloud_enabled'] is False
source=cache/('ruckig-'+provenance['revision'])
assert all(sha(source/n)==s for n,s in provenance['source_tree_sha256'].items())
result['native_source_and_binary_hashes_verified']=True
exports=load('ruckig-primary-exports.json')
def strip(o):
    if isinstance(o,list):return [strip(x) for x in o]
    if isinstance(o,dict):return {k:strip(v) for k,v in o.items() if k not in ['input','time_representation','binary_time_metadata']}
    return o

def reference_at(schedule,t):
    pieces=schedule['pieces'];starts=[Q(p['start_exact']) for p in pieces];k=min(bisect_right(starts,t)-1,len(pieces)-1)
    p=pieces[max(0,k)];z=t-Q(p['start_exact']);d=list(map(Q,[p[k] for k in ['p','v','a','jerk','snap']]))
    return [float(sum(d[i]*z**(i-k)/factorial(i-k) for i in range(k,5))) for k in range(4)]
for case in spec['cases']:
    if case['role']!='primary':continue
    name=case['id'];events=recovered[name];plans=exports[name];assert len(plans)==len(events)
    state=[0.,0.,0.];target=Q(0);rebuilt_pieces=[];native_commits=[]
    if events[0][0]>0:rebuilt_pieces.append((Q(0),events[0][0],[0.,0.,0.,0.,0.],'initial_rest'))
    for k,((tau,delta),saved) in enumerate(zip(events,plans)):
        stop=events[k+1][0] if k+1<len(events) else Q(case['end_s']);target+=delta;elapsed=float(stop-tau)
        assert Q(saved['commit_rational'])==tau and Q(saved['executed_until_rational'])==stop
        assert saved['plan']['input']=={'state':state,'target':float(target),'queries':[elapsed]}
        args=[str(exporter)]+[format(float(x),'.17g') for x in [*state,target,elapsed]]
        fresh=json.loads(subprocess.check_output(args,text=True));assert fresh==strip(saved['plan']),(name,k)
        native_commits.append((float(tau),float(target)))
        for p in fresh['phases']:
            stored=next(x for x in saved['plan']['phases'] if x['kind']==p['kind'] and x.get('index')==p.get('index'))
            for key,meta in stored['binary_time_metadata'].items():
                assert Q(meta['ratio'])==Q(p[key]) and float.fromhex(meta['hex'])==p[key]
            if p['duration']<=0 or p['start']>=elapsed:continue
            left=tau+Q(p['start']);right=min(stop,tau+Q(p['end']));assert right>left
            rebuilt_pieces.append((left,right,[p[n] for n in ['p','v','a','jerk']]+[0.],f'plan_{k}_{p["kind"]}_{p["index"]}'))
            if right-left<Q(1,10**12):result['tiny_executed_phases'].append({'case':name,'plan':k,'start':str(left),'end':str(right),'duration_exact':str(right-left),'float_absolute_clock_collapses':float(left)==float(right)})
        if fresh['duration']<elapsed:
            p=fresh['tail'];rebuilt_pieces.append((tau+Q(p['start']),stop,[p[n] for n in ['p','v','a','jerk']]+[0.],f'plan_{k}_extrapolated_tail'))
        samples=[r for r in fresh['samples'] if r['t']==elapsed];assert len(samples)==1
        state=[samples[0][n] for n in ['p','v','a']]
    schedule=schedules[name,'ruckig'];assert len(schedule['pieces'])==len(rebuilt_pieces)
    for actual,rebuilt in zip(schedule['pieces'],rebuilt_pieces):
        assert Q(actual['start_exact'])==rebuilt[0] and Q(actual['end_exact'])==rebuilt[1]
        assert [actual[k] for k in ['p','v','a','jerk','snap']]==rebuilt[2] and actual['origin']==rebuilt[3]
    result['native_export_reproduction'][name]={'plans_reproduced':len(plans),'executed_pieces_reproduced':len(rebuilt_pieces)}
    # An additional native replay retains at_time state using native absolute clocks.
    times={float(Q(k,2000)) for k in range(int(Q(case['end_s'])*2000)+1)}
    for piece in schedule['pieces']:
        for key in ['start_exact','end_exact']:
            t=float(Q(piece[key]));times.add(t)
            if t>0:
                times.add(nextafter(t,0.))
                times.add(nextafter(t,inf))
    times=sorted(t for t in times if 0<=t<=float(Q(case['end_s'])))
    text=str(len(native_commits))+'\n'+'\n'.join(format(t,'.17g')+' '+format(g,'.17g') for t,g in native_commits)+'\n'+str(len(times))+'\n'+'\n'.join(format(t,'.17g') for t in times)+'\n'
    (HERE/('native-'+name+'-input.txt')).write_text(text)
    out=subprocess.check_output([str(native)],input=text,text=True);(HERE/('native-'+name+'-output.json')).write_text(out)
    data=json.loads(out);assert len(data['commits'])==len(plans) and len(data['queries'])==len(times)
    maxres=[0.]*3;branches=[];commitres=[0.]*3;boundaries=[Q(p['start_exact']) for p in schedule['pieces']]+[Q(schedule['horizon_exact'])]
    for row in data['queries']:
        t=Q(row['time']);q=reference_at(schedule,t)
        for i,key in enumerate(['q','qv','qa']):maxres[i]=max(maxres[i],abs(row[key]-q[i]))
        if row['jerk']!=q[3]:branches.append({'time':row['time'],'native_jerk':row['jerk'],'canonical_jerk':q[3],'nearest_boundary_distance_s':float(min(abs(t-b) for b in boundaries))})
    for row,p in zip(data['commits'],plans):
        for i,key in enumerate(['current_p','current_v','current_a']):commitres[i]=max(commitres[i],abs(row[key]-p['plan']['input']['state'][i]))
    assert all(x<y for x,y in zip(maxres,[1e-8,1e-8,1e-10]))
    assert all(x['nearest_boundary_distance_s']<1e-12 for x in branches)
    result['native'][name]={'query_count':len(times),'commit_count':len(plans),'max_q_v_a_disagreement':maxres,'max_commit_q_v_a_disagreement':commitres,'jerk_branch_differences':branches,'state_tolerances_pass':True,'clock':'Native double absolute commit subtraction versus exact rational commit plus native binary offset; not bit-identical schedules.'}
    dump('schedule-review.json',result)
# Four smoke cases: regenerate their stored inputs and inspect the public piece reconstruction.
smokes=load('ruckig-smoke-exports.json');result['smokes']={}
for name,saved in smokes.items():
    inp=saved['input'];args=[str(exporter)]+[format(float(x),'.17g') for x in [*inp['state'],inp['target'],*inp['queries']]]
    fresh=json.loads(subprocess.check_output(args,text=True));assert fresh==strip(saved)
    positive=[p for p in fresh['phases'] if p['duration']>0];maxres=[0.]*3
    for row in fresh['samples']:
        t=row['t'];p=fresh['tail'] if t>=fresh['duration'] else next(p for p in reversed(positive) if p['start']<=t)
        z=Q(t)-Q(p['start']);der=[Q(p[n]) for n in ['p','v','a','jerk']]
        q=[float(sum(der[i]*z**(i-k)/factorial(i-k) for i in range(k,4))) for k in range(3)]
        for i,key in enumerate(['p','v','a']):maxres[i]=max(maxres[i],abs(row[key]-q[i]))
    assert all(x<=y for x,y in zip(maxres,[1e-8,1e-8,1e-10]))
    result['smokes'][name]={'export_reproduced':True,'samples':len(fresh['samples']),'max_q_v_a_error':maxres,'active_brake':fresh['brake_duration']>0}
result['all_artifacts_unchanged']=all(sha(B/n)==v for n,v in manifest['files'].items())
result['status']='complete';result['passed']=result['all_artifacts_unchanged'];dump('schedule-review.json',result)
print(json.dumps({'passed':result['passed'],'case_count':len(result['cases']),'native_queries':sum(x['query_count'] for x in result['native'].values()),'reproduced_primary_plans':sum(x['plans_reproduced'] for x in result['native_export_reproduction'].values()),'tiny_executed_phases':result['tiny_executed_phases']}))
