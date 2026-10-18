"""Local exporter reconstruction checks. These are builder checks, not independent review."""
from pathlib import Path
from fractions import Fraction
import json, math, subprocess

HERE=Path(__file__).resolve().parent
LIMITS=[1e-8,1e-8,1e-10]

def export(state,target,queries=()):
    args=[str(HERE/'.cache/ruckig_export')]+[format(float(x),'.17g') for x in [*state,target,*queries]]
    run=subprocess.run(args,text=True,capture_output=True,check=True)
    result=json.loads(run.stdout)
    result['time_representation']='JSON numbers round-trip native binary doubles. Absolute replay time is rational commit time plus the exported native cumulative boundary, not a sum of exact phase durations and not bit-identical at_time execution.'
    for phase in result['phases']:
        phase['binary_time_metadata']={k:{'hex':phase[k].hex() if isinstance(phase[k],float) else float(phase[k]).hex(),'ratio':str(Fraction(phase[k]))} for k in ['start','end','duration','native_t_sum'] if k in phase}
    result['input']={'state':list(state),'target':target,'queries':list(queries)}
    return result

def polynomial(phase,t):
    s=t-phase['start']; j=phase['jerk']; p,v,a=[phase[k] for k in ['p','v','a']]
    return [p+v*s+a*s*s/2+j*s*s*s/6,v+a*s+j*s*s/2,a+j*s]

def reconstruct(plan,t):
    if t>=plan['duration']:return polynomial(plan['tail'],t)
    positive=[p for p in plan['phases'] if p['duration']>0]
    selected=[p for p in positive if p['start']<=t]
    if not selected: raise AssertionError(('uncovered start',t,plan))
    return polynomial(selected[-1],t)

def validate(plan):
    maxima=[0.,0.,0.]
    for sample in plan['samples']:
        actual=[sample[k] for k in ['p','v','a']]
        residual=[abs(x-y) for x,y in zip(reconstruct(plan,sample['t']),actual)]
        maxima=[max(a,b) for a,b in zip(maxima,residual)]
    positive=[p for p in plan['phases'] if p['duration']>0]
    continuity=[0.,0.,0.]
    for left,right in zip(positive,positive[1:]+[plan['tail']]):
        residual=[abs(x-right[k]) for x,k in zip(polynomial(left,right['start']),['p','v','a'])]
        continuity=[max(a,b) for a,b in zip(continuity,residual)]
    final=[plan['tail'][k] for k in ['p','v','a']]
    endpoint=[abs(final[0]-plan['input']['target']),abs(final[1]),abs(final[2])]
    assert plan['accel_duration']==0
    for values in [maxima,continuity,endpoint]:assert all(a<=b for a,b in zip(values,LIMITS)),(values,LIMITS)
    return {'passed':True,'samples':len(plan['samples']),'reconstruction_max_abs':maxima,'continuity_max_abs':continuity,'endpoint_abs_residual':endpoint,'active_brake':plan['brake_duration']>0,'zero_duration_phases':sum(p['duration']==0 for p in plan['phases'])}

def queried_state(plan,t):
    row=min(plan['samples'],key=lambda x:abs(x['t']-t))
    assert row['t']==t,(row['t'],t)
    return [row[k] for k in ['p','v','a']]

def smoke():
    plans={}
    plans['rest_to_rest']=export([0.,0.,0.],.02,[.03])
    accelerating=queried_state(plans['rest_to_rest'],.03)
    plans['replan_accelerating']=export(accelerating,-.01)
    switch=next(p['start']+p['duration'] for p in plans['rest_to_rest']['phases'] if p['duration']>0 and p['kind']=='main')
    base=export([0.,0.,0.],.02,[switch])
    plans['replan_at_switch']=export(queried_state(base,switch),.005)
    plans['active_brake']=export([0.,.15,.6],.02)
    results={name:validate(plan) for name,plan in plans.items()}
    assert results['active_brake']['active_brake']
    assert accelerating[2]!=0
    (HERE/'ruckig-smoke-exports.json').write_text(json.dumps(plans,indent=2)+'\n')
    result={'passed':True,'limits_position_velocity_acceleration':LIMITS,'status':'builder reconstruction smoke only; independent review pending','fixtures':results}
    (HERE/'ruckig-smoke-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':smoke()
