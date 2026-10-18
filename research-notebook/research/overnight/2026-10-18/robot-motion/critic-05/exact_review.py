from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
import copy,hashlib,importlib.util,json,sys
HERE=Path(__file__).resolve().parent;B=HERE.parent/'builder-05'
sys.dont_write_bytecode=True;sys.path.insert(0,str(B))
import client

def jet(events,h,t,d):
    return sum((delta*sum(((-1)**k*comb(4,k)*max((t-tau)/h-k,F(0))**(4-d) for k in range(5)),F(0))/factorial(4-d)/h**d for tau,delta in events),F(0))
def canon(o):
    if isinstance(o,dict):return {k:(o[k] if k=='version' else canon(o[k])) for k in sorted(o)}
    if isinstance(o,list):return [canon(v) for v in o]
    return F(o)
def candidate(p,tau):
    b=p['base'];task=p['task'];h=b['width'];c=task['request'];D=task['deadline'];es=b['events']+[[tau,p['delta']]]
    if h<=0 or min(task['speed'],task['accel'],task['jerkLimit'])<0:return False
    if tau<c or any(e[0]+4*h>D for e in es):return False
    knots=sorted(set([c]+[t+k*h for t,_ in es for k in range(5) if t+k*h>=c]))
    if any(abs(jet(es,h,t,3))>task['jerkLimit'] or abs(jet(es,h,t,2))>task['accel'] or abs(jet(es,h,t,1))>task['speed'] for t in knots):return False
    for l,r in zip(knots,knots[1:]):
        vl,vr=jet(es,h,l,1),jet(es,h,r,1);al,ar=jet(es,h,l,2),jet(es,h,r,2)
        if max(abs(vl+(r-l)*al/3),abs(vr-(r-l)*ar/3))>task['speed']:return False
        jl,jr=jet(es,h,l,3),jet(es,h,r,3)
        if jl!=jr:
            z=l-jl*(r-l)/(jr-jl)
            if l<z<r and abs(jet(es,h,z,2))>task['accel']:return False
    return True

def decision(v):
    v=canon(v);p=v['pending'];b=v['liveBase'];t=v['liveTask'];tm=v['timing']
    goal=p['base']['offset']+sum((e[1] for e in p['base']['events']),F(0))
    chosen=next((tau for tau in p['candidates'] if candidate(p,tau)),None)
    detail={'delta':p['delta']==p['task']['goal']-goal,'selection':chosen==p['execution'],
      'base':b==p['base'],'task':t==p['task'],'time':p['task']['request']<=tm['completion']<=tm['commitTime'] and 0<=tm['dispatch'] and tm['commitTime']+tm['dispatch']<=p['execution']}
    return {'accept':all(detail.values()),'checks':detail,'chosen':str(chosen)}

def main():
    records=[]
    for file in sorted((B/'clients').glob('*.json')):
        r=decision(json.loads(file.read_text()));r['case']=file.stem;records.append(r)
        assert r['accept']==(file.stem=='on-time'),r
    v=json.loads((B/'clients/on-time.json').read_text());extra=[]
    changes=[('exact_dispatch_boundary',('timing','commitTime'),'61/100',True),
      ('overrun',('timing','dispatch'),'3/50',False),
      ('completion_after_commit',('timing','completion'),'3/5',False),
      ('completion_before_request',('timing','completion'),'1/2',False),
      ('negative_dispatch',('timing','dispatch'),'-1/100',False),
      ('retimed_execution',('pending','execution'),'13/25',False),
      ('wrong_delta',('pending','delta'),'0',False),
      ('missing_candidate',('pending','candidates'),['13/25'],False),
      ('changed_width',('liveBase','width'),'1/4',False),
      ('changed_speed',('liveTask','speed'),'1/100',False),
      ('changed_deadline',('liveTask','deadline'),'13/10',False),
      ('reused_version_different_offset',('liveBase','offset'),'1/1000',False)]
    for name,where,value,want in changes:
        x=copy.deepcopy(v);x[where[0]][where[1]]=value;r=decision(x);r['case']=name;assert r['accept']==want,r;extra.append(r)
    # These independently recomputed reference values diagnose lost contracts.
    h=F(1,5);old=[(F(11,50),F(1,50))];good=old+[(F(31,50),F(-1,50))]
    double=good+[(F(31,50),F(-1,50))];moved=old+[(F(13,25),F(-1,50))]
    late=jet(good,h,F(7,10),0)-jet(old,h,F(7,10),0)
    assert late==F(-8,375000)
    assert jet(double,h,F(17,10),0)==F(-1,50)
    assert jet(moved,h,F(77,100),2)==F(-21,32)
    assert [jet(good,h,F(31,50),d) for d in range(4)]==[jet(old,h,F(31,50),d) for d in range(4)]
    malformed=[]
    rationals=['','+1',' 1','1 ','0.5','1e2','1/-2','1/0','1//2','0x1','NaN','Infinity','1\n','1\u0000','1; import os',0,1.0,True,None,'9'*129]
    for v in rationals:
        try:client.rat(v)
        except (ValueError,TypeError,ZeroDivisionError) as e:malformed.append({'kind':'rational','input':repr(v),'exception':type(e).__name__})
        else:raise AssertionError(('accepted rational',v))
    for v in [-1,True,False,1.0,'1',None,{},[]]:
        try:client.version(v)
        except (ValueError,TypeError) as e:malformed.append({'kind':'version','input':repr(v),'exception':type(e).__name__})
        else:raise AssertionError(('accepted version',v))
    for v,want in [('0002/0004','(1/2:ℚ)'),('-0','(0/1:ℚ)'),('-6/3','(-2/1:ℚ)'),('1','(1/1:ℚ)')]:assert client.rat(v)==want
    v=json.loads((B/'clients/on-time.json').read_text())
    bads=[]
    for name,replace in [('base_wrong_object',lambda x:x.update(liveBase=[])),
      ('event_wrong_arity',lambda x:x['liveBase'].update(events=[['1']])),
      ('event_not_list',lambda x:x['liveBase'].update(events='1')),
      ('candidate_not_list',lambda x:x['pending'].update(candidates='1')),
      ('task_unknown_field',lambda x:x['liveTask'].update(unknown='1')),
      ('missing_field',lambda x:x['timing'].pop('dispatch'))]:
        z=copy.deepcopy(v);replace(z)
        try:client.pending(z['pending']);client.base(z['liveBase']);client.task(z['liveTask']);client.timing(z['timing'])
        except (ValueError,TypeError,KeyError) as e:bads.append({'case':name,'exception':type(e).__name__})
        else:raise AssertionError(name)
    dup=json.loads('{"goal":"0","goal":"1/200"}')
    assert dup['goal']=='1/200'
    result={'status':'PASS','method':'independent Fraction FIR derivative extrema and Bernstein test; original client parser tested separately','original_six_decisions':records,'boundary_decisions':extra,'exact_lost_contracts':{'late_position_change':str(late),'duplicate_final_position':str(jet(double,h,F(17,10),0)),'retimed_acceleration':str(jet(moved,h,F(77,100),2))},'malformed_rationals_versions':malformed,'malformed_structures':bads,'parser_acceptance_boundaries':['exact rational strings normalize before Lean; leading zeros and negative zero accepted','Python json.loads accepts duplicate keys with last value winning; not formally verified input semantics','negative widths/limits/times are representable and need the Lean semantic gate; parsing alone does not ensure safety'],'no_clock_performance_or_hardware_claim':True}
    (HERE/'exact-review-result.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
