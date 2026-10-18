"""Build the frozen shared input schedule and all executed reference segments."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import hashlib,json,shutil
from ruckig_checks import export,validate,queried_state

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

def ruckig(events,end):
    pieces=[];plans=[];results=[];state=[0.,0.,0.];target=Q(0)
    if events[0][0]>0:pieces.append(ordinary_piece(0,events[0][0],[0,0,0,0,0],'initial_rest'))
    for index,(tau,delta) in enumerate(events):
        target+=delta; stop=events[index+1][0] if index+1<len(events) else end
        duration=float(stop-tau)
        plan=export(state,float(target),[duration])
        check=validate(plan);check.update({'commit':str(tau),'index':index})
        results.append(check)
        plans.append({'commit_rational':str(tau),'executed_until_rational':str(stop),'plan':plan})
        for phase in plan['phases']:
            if phase['duration']<=0 or phase['start']>=duration:continue
            start=tau+Q(phase['start']);finish=min(stop,tau+Q(phase['end']))
            assert finish>start,('positive source phase has no exact interval',phase)
            pieces.append(ordinary_piece(start,finish,[phase[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{index}_{phase["kind"]}_{phase["index"]}'))
        if plan['duration']<duration:
            tail=plan['tail']; start=tau+Q(tail['start'])
            pieces.append(ordinary_piece(start,stop,[tail[k] for k in ['p','v','a','jerk']]+[0.],f'plan_{index}_extrapolated_tail'))
        state=queried_state(plan,duration)
    return pieces,plans,results

def main():
    assert json.loads((HERE/'ruckig-smoke-results.json').read_text())['passed']
    for name in ['fixed-streams.json','reference-checks.json','reference-enclosures.json']:
        destination=HERE/('frozen-'+name)
        shutil.copyfile(LEAD/name,destination)
        assert sha(destination)==sha(LEAD/name)
    spec=json.loads((HERE/'frozen-fixed-streams.json').read_text())
    checks=json.loads((HERE/'frozen-reference-checks.json').read_text())
    checked={x['case']:x for x in checks['cases']}
    schedules=[];exports={};validation={}
    for case in spec['cases']:
        if case['role']!='primary':continue
        row=checked[case['id']]
        events=[(Q(x['time_s']),Q(x['delta_m'])) for x in row['accepted_events']]
        end=Q(case['end_s']);h=Q(spec['h_s']);tick=Q(spec['commit_tick_s'])
        # Fixed scheduler consistency. Every payload at a sequence is unique.
        sequences={}
        for packet in case['packets']:
            seq=packet['sequence'];payload=(packet['observed_s'],packet['ready_s'],packet['target_m'])
            assert seq not in sequences or sequences[seq]==payload
            sequences[seq]=payload
        for outcome in row['outcomes']:
            c=Q(outcome['commit_s']);ready=Q(outcome['ready_s'])
            assert ready<=c<ready+tick and c/tick==(c/tick).numerator//(c/tick).denominator
        refs={'raw':raw(events,end),'fir':fir(events,h,end)}
        refs['ruckig'],exports[case['id']],validation[case['id']]=ruckig(events,end)
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
            schedules.append({'method':method,'case':case['id'],'horizon':float(end),'horizon_exact':str(end),'deadline':float(Q(case['deadline_s'])),'deadline_exact':case['deadline_s'],'truth':[{'time':float(Q(x['time_s'])),'time_exact':x['time_s'],'position':float(Q(x['position_m']))} for x in case['truth']],
                              'common_events':[{'time':float(time),'time_exact':str(time),'labels':labels} for time,labels in sorted(common.items())],
                              'admissions':row['outcomes'],'final_accepted_goal':float(Q(row['final_accepted_goal_m'])),'pieces':pieces})
    write('reference-schedules.json',{'status':'floating polynomial schedules; exact FIR coefficients retained separately; synthetic streams','schedules':schedules})
    write('ruckig-primary-exports.json',exports)
    write('ruckig-primary-validation.json',{'passed':True,'status':'builder check only','cases':validation})
    negative=[x for x in checks['cases'] if x['role']!='primary']
    write('retained-negative-cases.json',{'status':'frozen exact reference outcomes only; no extra plant cases','cases':negative})
    print(json.dumps({'reference_schedules':len(schedules),'ruckig_plans':sum(len(x) for x in exports.values()),'all_reconstruction_limits_passed':True,'negative_cases_retained':len(negative)},indent=2))

if __name__=='__main__':main()
