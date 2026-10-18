"""Mutation controls for the stored-polynomial checker, not optimizer reruns."""
from pathlib import Path
from fractions import Fraction as F
import json
from solve import validate

HERE=Path(__file__).resolve().parent
candidate=json.loads((HERE/'n90_cap10mm.json').read_text())
nodes=list(map(F,candidate['corrected_jerk_nodes_SI']))
initial=[F(77,19200),F(23,480),F(5,16)]
dt=F(1,100)
tests=[]
for name,change,cap,expected in [
    ('tighter_travel_cap',None,F(9,1000),'position_cap'),
    ('outside_jerk_bound',(1,F(-8)),F(1,100),'jerk'),
    ('nonzero_terminal_jerk',(-1,F(1,1000)),F(1,100),'terminal_or_initial_jerk'),
    ('perturbed_interior_jerk',(40,nodes[40]+F(1,1000)),F(1,100),'terminal_state'),
]:
    mutated=list(nodes)
    if change:mutated[change[0]]=change[1]
    result,_=validate(mutated,dt,initial,cap)
    conditions={item['condition'] for item in result['violations']}
    assert not result['passed'] and expected in conditions,(name,conditions)
    tests.append({'name':name,'mutation':None if change is None else [change[0],str(change[1])],
                  'cap':str(cap),'expected_rejection':expected,'passed':True,
                  'violations':result['violations']})
(HERE/'negative-controls.json').write_text(json.dumps({'tests':tests},indent=2)+'\n')
print('Four mutated candidates rejected for the intended conditions.')
