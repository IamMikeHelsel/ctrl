#!/usr/bin/env python3
"""Independent rational polynomial check. This does not simulate the plant."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
SRC = ROOT.parent / 'analyst'
record = json.loads((SRC / 'exact-task-check.json').read_text())
task = record['fixed_stop_task']

def exact(x):
    return F(x['exact']) if isinstance(x, dict) else F(x)

def integrate(p, constant):
    return [constant] + [a / (i + 1) for i, a in enumerate(p)]

def evaluate(p, t):
    value = F(0)
    for coefficient in reversed(p):
        value = value * t + coefficient
    return value

def derivative(p):
    return [i * p[i] for i in range(1, len(p))]

def encode(x):
    if isinstance(x, F): return str(x)
    if isinstance(x, dict): return {k: encode(v) for k,v in x.items()}
    if isinstance(x, (list, tuple)): return [encode(v) for v in x]
    return x

# Construct each segment by repeated integration of a constant polynomial.
# Do not use the analyst's closed-form step function.
state = [F(0), F(0), F(0), F(10)]
time = F(0)
phase_checks = []
for phase in task['constant_snap_phases']:
    assert time == exact(phase['start'])
    assert state == list(map(exact, phase['state_start']))
    dt, snap = exact(phase['duration']), exact(phase['snap'])
    polys = [[snap]]
    for constant in reversed(state):
        polys.append(integrate(polys[-1], constant))
    q, v, a, j = reversed(polys[1:])
    extrema_times = [F(0), dt]
    if snap and 0 <= -state[3]/snap <= dt:
        extrema_times.append(-state[3]/snap)
    acceleration_values = [evaluate(a, t) for t in extrema_times]
    assert min(acceleration_values) >= 0
    assert max(acceleration_values) <= 3
    assert max(abs(evaluate(j, t)) for t in [F(0), dt]) <= 10
    assert abs(snap) <= 400
    state = [evaluate(p, dt) for p in [q, v, a, j]]
    assert state == list(map(exact, phase['state_end']))
    phase_checks.append({'name':phase['name'], 'end':state,
        'acceleration_extrema':acceleration_values})
    time += dt

V = state[1]
L = F(7,10)
cruise = (F(3,5)-state[0]-V*L/2)/V
assert cruise == exact(task['cruise_duration']) > 0
brake_start = time+cruise
brake_q = state[0]+V*cruise
assert brake_start == exact(task['brake_start'])

# Derive the brake by integrating its velocity polynomial.
vpoly = list(map(F, [1,0,0,-10,15,-6]))
qpoly = integrate(vpoly, F(0))
apoly = derivative(vpoly)
jpoly = derivative(apoly)
spoly = derivative(jpoly)
assert qpoly == list(map(exact, task['brake_normalized_position_coefficients']))
assert apoly == list(map(F,[0,0,-30,60,-30]))
assert jpoly == list(map(F,[0,-60,180,-120]))
assert spoly == list(map(F,[-60,360,-360]))
assert evaluate(qpoly,F(1)) == F(1,2)
assert all(evaluate(p,F(1)) == 0 for p in [vpoly,apoly,jpoly])
assert [evaluate(p,F(0)) for p in [vpoly,apoly,jpoly]] == [1,0,0]
assert brake_q+V*L*evaluate(qpoly,F(1)) == F(3,5)
stop = brake_start+L
assert stop == F(10491307,7508900) < F(3,2)

# Whole-interval bounds. Put z=y(1-y), 0<=z<=1/4.
# a=-30 V z^2/L. j^2=3600 V^2 z^2(1-4z)/L^4.
# The cubic has its only interior maximum at z=1/6.
# snap=-60 V(1-6z)/L^3; its absolute factor is at most one.
amax = 30*V*F(1,4)**2/L
jmax2 = 3600*V**2*F(1,6)**2*(1-4*F(1,6))/L**4
smax = 60*V/L**3
assert amax == F(10727,5120) < 3
assert jmax2 == F(115068529,1354752) < 100
assert smax == F(53635,392) < 400
assert 0 < V < 1

result = {'passed':True, 'method':'Independent repeated polynomial integration and exact extrema; no plant propagation',
    'phase_checks':phase_checks,'brake_start':brake_start,'brake_position':brake_q,
    'reference_endpoint':[F(3,5),F(0),F(0),F(0)],'stop_time':stop,
    'slack':F(3,2)-stop,'velocity_max':V,'brake_a_abs_max':amax,
    'brake_j_abs_max_squared':jmax2,'brake_snap_abs_max':smax,
    'whole_interval_reason':'Initial blend a>=0 so velocity increases to V. Cruise v=V. Brake a<=0 with v endpoints V and zero. Thus v>=0 and q increases to 3/5.',
    'regularity':'Reference jerk continuous; right snap is piecewise polynomial and may jump at joins. No two-sided snap claim at joins.',
    'initial_command_checks':{'direct_u':F(5,48),'filtered_u':F(0),
        'direct_actual_jerk':F(137,15),'filtered_actual_jerk':F(4,5)}}
manifest=json.loads((SRC/'artifact-sha256.json').read_text())
assert all(hashlib.sha256((SRC/name).read_bytes()).hexdigest()==digest for name,digest in manifest.items())
(ROOT/'independent-check.json').write_text(json.dumps(encode(result),indent=2)+'\n')
print(json.dumps(encode(result),indent=2))
