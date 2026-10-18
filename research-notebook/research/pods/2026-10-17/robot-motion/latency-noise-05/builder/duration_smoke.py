"""Independent rational polynomial reconstruction of minimum-duration native queries.
This is a separate arithmetic path in the builder, not an independent reviewer.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
from ruckig_checks import export,queried_state
HERE=Path(__file__).resolve().parent

def check(plan):
    assert plan['minimum_duration']==.8 and plan['duration']>=.8
    assert plan['accel_duration']==0
    positive=[p for p in plan['phases'] if p['duration']>0]
    worst=[Q(0)]*3
    for row in plan['samples']:
        t=Q(row['t'])
        phase=plan['tail'] if t>=Q(plan['duration']) else [p for p in positive if Q(p['start'])<=t][-1]
        s=t-Q(phase['start']);p,v,a,j=[Q(phase[k]) for k in ['p','v','a','jerk']]
        values=[p+s*v+s*s*a/2+s**3*j/6,v+s*a+s*s*j/2,a+s*j]
        worst=[max(old,abs(value-Q(row[k]))) for old,value,k in zip(worst,values,['p','v','a'])]
    limits=[Q(1,10**8),Q(1,10**8),Q(1,10**10)]
    assert all(value<=limit for value,limit in zip(worst,limits))
    tail=plan['tail'];endpoint=[abs(tail['p']-plan['input']['target']),abs(tail['v']),abs(tail['a'])]
    assert all(value<=float(limit) for value,limit in zip(endpoint,limits))
    return {'passed':True,'query_count':len(plan['samples']),'maximum_state_residual_exact':[str(x) for x in worst],
            'maximum_state_residual_float':[float(x) for x in worst],'actual_native_duration_s':plan['duration'],'requested_minimum_s':.8,
            'native_duration_adjustment_above_minimum_s':plan['duration']-.8,'endpoint_residual':endpoint}

def main():
    first=export([0.,0.,0.],.02,[.23],minimum_duration=.8)
    second=export(queried_state(first,.23),-.01,minimum_duration=.8)
    results={name:check(plan) for name,plan in [('rest_step',first),('retained_accelerating_replan',second)]}
    (HERE/'duration-smoke-exports.json').write_text(json.dumps({'rest_step':first,'retained_accelerating_replan':second},indent=2)+'\n')
    (HERE/'duration-smoke-results.json').write_text(json.dumps({'passed':True,'status':'independent rational reconstruction path within builder; no physical plant run','limits':[1e-8,1e-8,1e-10],'fixtures':results},indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
