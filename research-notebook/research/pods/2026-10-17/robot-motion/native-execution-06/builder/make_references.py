"""Build the frozen shared input schedule and all executed reference segments."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,comb
import hashlib,json,shutil,subprocess
from ruckig_checks import validate
from knot_check import remaining_check

HERE=Path(__file__).resolve().parent
ROBOT=HERE.parents[1]
LEAD=ROBOT/'lead-01'
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def state_at(piece,t):
    s=float(Q(t)-Q(piece['start_exact'])); p,v,a,j,snap=[piece[k] for k in ['p','v','a','jerk','snap']]
    return [p+v*s+a*s*s/2+j*s**3/6+snap*s**4/24,v+a*s+j*s*s/2+snap*s**3/6,a+j*s+snap*s*s/2,j+snap*s,snap]

def ordinary_piece(start,end,state,origin,exact=None):
    result={'start':float(start),'end':float(end),'start_exact':str(Q(start)),'end_exact':str(Q(end)),**dict(zip(['p','v','a','jerk','snap'],map(float,state))),'origin':origin}
    if exact is not None:result['rational_derivatives_at_start']=[str(x) for x in exact]
    return result

def fir(events,h,end):
    knots=sorted({Q(0),end}|{t+i*h for t,d in events for i in range(5) if 0<=t+i*h<=end})
    pieces=[]
    for left,right in zip(knots,knots[1:]):
        mid=(left+right)/2
        ds=[]
        for order in range(5):
            ds.append(sum((delta*coefficient*(left-(tau+i*h))**(4-order)/Q(factorial(4-order))/h**4
                           for tau,delta in events for i,coefficient in enumerate([1,-4,6,-4,1]) if tau+i*h<mid),Q(0)))
        pieces.append(ordinary_piece(left,right,ds,'exact_four_box',ds))
    return pieces

def raw(events,end):
    pieces=[]; value=Q(0); start=Q(0)
    for time,delta in events:
        if time>start:pieces.append(ordinary_piece(start,time,[value,0,0,0,0],'accepted_position_step'))
        value+=delta;start=time
    if start<end:pieces.append(ordinary_piece(start,end,[value,0,0,0,0],'accepted_position_step'))
    return pieces

def ruckig(events,end,minimum_duration=0.,identity='native'):
    # Only native_execution.cpp computes state carried into another native plan.
    target=Q(0);commits=[]
    for tau,delta in events:
        target+=delta;commits.append((tau,float(tau),float(target)))
    text=str(len(commits))+'\n'+''.join(f'{t:.17g} {g:.17g}\n' for _,t,g in commits)
    folder=HERE/'native-plans';folder.mkdir(exist_ok=True)
    (folder/(identity+'-input.txt')).write_text(text)
    run=subprocess.run([str(HERE/'.cache/native_execution'),str(minimum_duration),format(float(end),'.17g')],input=text,text=True,capture_output=True,check=True)
    (folder/(identity+'-output.json')).write_text(run.stdout)
    native=json.loads(run.stdout);assert len(native['plans'])==len(commits)
    pieces=[];plans=[];results=[]
    if commits[0][1]>0:pieces.append(ordinary_piece(0,Q(commits[0][1]),[0,0,0,0,0],'initial_rest'))
    for index,(record,(scheduler_tau,native_tau,target)) in enumerate(zip(native['plans'],commits)):
        assert record['native_commit']==native_tau and record['target']==target
        tau=Q(native_tau);stop=Q(commits[index+1][1]) if index+1<len(commits) else end
        duration=float(stop-tau);plan=record['plan']
        plan['input']={'state':record['current_state'],'target':target,'queries':[record['native_elapsed_to_next_commit_or_horizon']],'minimum_duration':minimum_duration}
        plan['time_representation']='Native C++ state carry with absolute double subtraction. Physical origin is exact binary native commit plus exact exported cumulative phase boundary. Not bit-identical at_time for arbitrary queries.'
        for phase in plan['phases']:
            phase['binary_time_metadata']={k:{'hex':float(phase[k]).hex(),'ratio':str(Q(phase[k]))} for k in ['start','end','duration','native_t_sum'] if k in phase}
        check=validate(plan);check.update({'commit':str(scheduler_tau),'native_commit_exact':str(tau),'index':index})
        results.append(check)
        plans.append({'commit_rational':str(scheduler_tau),'native_commit_float':native_tau,'native_commit_exact':str(tau),'native_commit_hex':native_tau.hex(),
                      'native_minus_scheduler_time_exact':str(tau-scheduler_tau),'executed_until_rational':str(stop),
                      'native_elapsed_to_next_commit_or_horizon':record['native_elapsed_to_next_commit_or_horizon'],'plan':plan})
        for phase in plan['phases']:
            if phase['duration']<=0:continue
            start=tau+Q(phase['start']);finish=min(stop,tau+Q(phase['end']))
            assert Q(phase['end'])>=Q(phase['start']),('decreasing cumulative phase',phase)
            if finish<=start:continue # All phase metadata remains exported, including zero-measure positive t.
            pieces.append(ordinary_piece(start,finish,[phase[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{index}_{phase["kind"]}_{phase["index"]}'))
        tail=plan['tail'];start=tau+Q(tail['start'])
        if start<stop:
            pieces.append(ordinary_piece(start,stop,[tail[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{index}_extrapolated_tail'))
    return pieces,plans,results

def schedule_case(case,h,tick):
    groups={};sequences={}
    for packet in case['packets']:
        seq=packet['sequence'];payload=(packet['observed_s'],packet['ready_s'],packet['target_m'])
        assert seq not in sequences or sequences[seq]==payload
        sequences[seq]=payload
        ready=Q(packet['ready_s']);c=-(-ready//tick)*tick
        groups.setdefault(c,[]).append(packet)
    events=[];unguarded=[];value=Q(0);uvalue=Q(0);watermark=-1;outcomes=[];prefix=[];replans=[]
    for c,group in sorted(groups.items()):
        winner=max(group,key=lambda p:p['sequence'])
        for item in group:
            if item is not winner:outcomes.append({**item,'commit_s':str(c),'outcome':'coalesced_by_larger_sequence'})
        if winner['sequence']<=watermark:
            outcomes.append({**winner,'commit_s':str(c),'outcome':'stale_discard'});continue
        watermark=winner['sequence'];target=Q(winner['target_m']);delta=target-value
        candidate=events+([(c,delta)] if delta else [])
        guard=remaining_check(candidate,h,Q(15,2),c)
        ud=target-uvalue
        if ud:unguarded.append((c,ud))
        uvalue=target
        outcome={**winner,'commit_s':str(c),'age_at_commit_s':str(c-Q(winner['observed_s'])),'delta_m':str(delta),
                 'future_reference_jerk_peak_m_s3':str(guard['peak_abs']),'peak_time_s':str(guard['peak_time']),'checked_future_knots':len(guard['knots'])}
        if guard['passed']:
            events=candidate;value=target;replans.append((c,delta));outcome['outcome']='accepted'
        else:outcome['outcome']='jerk_rejected'
        outcomes.append(outcome)
        encode=lambda e:json.dumps([[str(t),str(d)] for t,d in e],separators=(',',':'))
        prefix.append({'commit_s':str(c),'guard_passed':guard['passed'],'histories_equal':events==unguarded,
                       'guarded_history_sha256':hashlib.sha256(encode(events).encode()).hexdigest(),'unguarded_history_sha256':hashlib.sha256(encode(unguarded).encode()).hexdigest()})
    return {'case':case['id'],'outcomes':outcomes,'events':events,'replans':replans,'final_accepted_goal':value,'ablation_prefixes':prefix,
            'guarded_equals_unguarded_all_prefixes':all(x['histories_equal'] for x in prefix)}

def exact_bounds(pieces):
    bounds={order:Q(0) for order in [1,2,3]}
    for piece in pieces:
        d=list(map(Q,piece['rational_derivatives_at_start']));width=Q(piece['end_exact'])-Q(piece['start_exact'])
        for order in [1,2,3]:
            mono=[d[order+k]*width**k/factorial(k) for k in range(5-order)];n=len(mono)-1
            bern=[sum(mono[k]*Q(comb(i,k),comb(n,k)) for k in range(i+1)) for i in range(n+1)]
            bounds[order]=max(bounds[order],*(abs(x) for x in bern))
    limits={1:Q(1,10),2:Q(1,2),3:Q(15,2)}
    assert all(bounds[k]<=limits[k] for k in bounds)
    return {'passed':True,'rational_Bernstein_sufficient_bounds':{str(k):str(v) for k,v in bounds.items()}}

def main():
    assert json.loads((HERE/'previous05-ruckig-smoke-results.json').read_text())['passed']
    assert json.loads((HERE/'previous05-duration-smoke-results.json').read_text())['passed']
    frozen=json.loads((HERE/'pre-run-input-manifest.json').read_text())
    for name,digest in frozen['files'].items():assert sha(HERE/name)==digest
    spec=json.loads((HERE/'packets.json').read_text())
    schedules=[];exports={};validation={};ablation=[];transcripts=[];enclosures={}
    for case in spec['cases']:
        end=Q(case['end_s']);h=Q(spec['h_s']);tick=Q(spec['commit_tick_s'])
        row=schedule_case(case,h,tick);events=row['events'];replans=row['replans']
        ablation.append({'case':case['id'],'initial_history_equal':True,'h_equal':'1/5','all_prefixes_equal':row['guarded_equals_unguarded_all_prefixes'],'prefixes':row['ablation_prefixes']})
        transcripts.append({'case':case['id'],'outcomes':row['outcomes'],'accepted_events':[[str(t),str(d)] for t,d in events],'final_accepted_goal_m':str(row['final_accepted_goal'])})
        refs={'raw':raw(events,end),'fir':fir(events,h,end)}
        enclosures[case['id']]=exact_bounds(refs['fir'])
        for method,minimum in [('ruckig',0.),('ruckig_min_08',.8)]:
            key=case['id']+'__'+method
            refs[method],exports[key],validation[key]=ruckig(replans,end,minimum,key)
        common={Q(0):['start'],end:['horizon'],Q(case['deadline_s']):['deadline']}
        def add(t,label):common.setdefault(Q(t),[]).append(label)
        for item in case['truth']:add(Q(item['time_s']),'truth_change')
        for item in case['packets']:
            add(Q(item['observed_s']),'observation');add(Q(item['ready_s']),'ready')
        for item in row['outcomes']:add(Q(item['commit_s']),'commit_'+item['outcome'])
        tail=max((t for t,d in events),default=Q(0))+4*h
        if tail<=end:add(tail,'fir_final_tail')
        for method,pieces in refs.items():
            assert Q(pieces[0]['start_exact'])==0 and Q(pieces[-1]['end_exact'])==end
            for a,b in zip(pieces,pieces[1:]):assert Q(a['end_exact'])==Q(b['start_exact']),(method,a,b)
            schedules.append({'method':method,'case':case['id'],'hold_required':case['id']!='persistent_goal','horizon':float(end),'horizon_exact':str(end),'deadline':float(Q(case['deadline_s'])),'deadline_exact':case['deadline_s'],'truth':[{'time':float(Q(x['time_s'])),'time_exact':x['time_s'],'position':float(Q(x['position_m']))} for x in case['truth']],
                              'common_events':[{'time':float(time),'time_exact':str(time),'labels':labels} for time,labels in sorted(common.items())],
                              'admissions':row['outcomes'],'final_accepted_goal':float(row['final_accepted_goal']),'pieces':pieces})
    write('reference-schedules.json',{'status':'native retained Ruckig plans with exact-binary execution origins; floating polynomial interpretation; raw/FIR unchanged; synthetic streams','schedules':schedules})
    write('ruckig-primary-exports.json',exports)
    write('ruckig-primary-validation.json',{'passed':True,'status':'builder check only','cases':validation})
    write('admission-transcripts.json',{'cases':transcripts})
    write('fir-exact-enclosures.json',enclosures)
    write('fir-ablation-equality.json',{'argument':'The initial target, h and complete signed event list agree on every prefix. The deterministic sum q(t)=g0+sum delta*F((t-tau)/h) is therefore identical for guarded and unguarded FIR on every executed prefix, and after the last update. This is a finite exact input/history identity, not another plant method or a general Python refinement proof.','cases':ablation})
    print(json.dumps({'reference_schedules':len(schedules),'ruckig_plans':sum(len(x) for x in exports.values()),'all_reconstruction_limits_passed':True,'guard_ablation_equal':all(x['all_prefixes_equal'] for x in ablation)},indent=2))

if __name__=='__main__':main()
