#!/usr/bin/env python3
"""Exact rational kinematics; no plant simulation or Lean verification.

Run from any directory. All generated evidence stays beside this script.
"""
from fractions import Fraction as F
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent

def step(q, dt, snap):
    x, v, a, j = q
    return (x + v*dt + a*dt**2/2 + j*dt**3/6 + snap*dt**4/24,
            v + a*dt + j*dt**2/2 + snap*dt**3/6,
            a + j*dt + snap*dt**2/2, j + snap*dt)

def data(value):
    if isinstance(value, F):
        return {"exact": str(value), "decimal": float(value)}
    if isinstance(value, dict):
        return {k: data(v) for k,v in value.items()}
    if isinstance(value, (list,tuple)):
        return [data(v) for v in value]
    return value

J, S, a0 = F(10), F(400), F(5,2)
h = 2*J/S
Tzero = a0/J+h
old_start = (F(5,192), F(5,16), a0, J)
old_endpoint = step((old_start[0],old_start[1],a0,-J), F(1,4), F(0))
ramp_end = step(old_start, h, -S)
zero_endpoint = step(ramp_end, a0/J, F(0))
assert ramp_end[2] == a0 and ramp_end[3] == -J
assert zero_endpoint == (F(1991,9600),F(181,240),F(0),-J)
assert old_endpoint[:3] == (F(5,32),F(5,8),F(0))
assert Tzero == F(3,10) > F(1,4)
assert zero_endpoint[0] > old_endpoint[0]
assert zero_endpoint[1] > old_endpoint[1]

# A distinct, fixed stop contract. The new goal is available only at t=1/4.
# During the 5 ms latency, the old +J reference continues unchanged.
arrival, latency, deadline = F(1,4), F(1,200), F(3,2)
execution = arrival+latency
initial = (F(0),F(0),F(0),J)
q_exec = step(initial, execution, F(0))
assert q_exec == (F(44217,1600000),F(2601,8000),F(51,20),J)
# Ramp +J -> -J; hold -J; ramp -J -> 0. End a=j=0.
d1, d2, d3 = 2*J/S, q_exec[2]/J-J/(2*S), J/S
assert d2 > 0
phases = []
q, t = initial, F(0)
for label,dt,snap in [("old_plan_and_latency",execution,F(0)),
                       ("jerk_reversal",d1,-S),
                       ("negative_jerk_hold",d2,F(0)),
                       ("jerk_to_zero",d3,S)]:
    q_end = step(q,dt,snap)
    phases.append({"name":label,"start":t,"duration":dt,"snap":snap,
                   "state_start":q,"state_end":q_end})
    q,t = q_end,t+dt
assert q == (F(8782613,38400000),F(75089,96000),F(0),F(0))
blend_end_time, blend_end = t,q
X,L = F(3,5),F(7,10)
V = q[1]
cruise = (X-q[0]-V*L/2)/V
assert cruise == F(3744927,30035600) > 0
q_brake = step(q,cruise,F(0))
brake_start = t+cruise
stop_time = brake_start+L
assert stop_time == F(10491307,7508900) < deadline

# For y=s/L in [0,1], the braking segment has
# v=V(1-10y^3+15y^4-6y^5), a=-(30V/L)y^2(1-y)^2,
# j=-(60V/L^2)y(1-y)(1-2y), snap=-(60V/L^3)(1-6y+6y^2).
# Its exact bounds follow from polynomial extrema, not a time grid:
# a maximum at y=1/2; j^2 maximum at y=(3+-sqrt(3))/6;
# |1-6y+6y^2|<=1. Since a<=0, v decreases from V to zero.
brake_a_bound = F(15,8)*V/L
brake_j_squared_bound = F(100,3)*V**2/L**4
brake_snap_bound = 60*V/L**3
blend_a_bound = q_exec[2] + J**2/(2*S)
assert blend_a_bound == F(107,40) < 3
assert 0 < V < 1
assert brake_a_bound < 3
assert brake_j_squared_bound < J**2
assert brake_snap_bound < S
assert q_brake[0]+V*L/2 == X
assert 0 <= q_brake[0] <= X

# Symbolic normalized polynomial integration, using rational coefficients.
# This checks exact differentiation and endpoints independently of step().
pos = [F(0),F(1),F(0),F(0),F(-5,2),F(3),F(-1)]
def deriv(p): return [i*p[i] for i in range(1,len(p))]
def ev(p,z): return sum(c*z**i for i,c in enumerate(p))
vp,ap,jp,sp = deriv(pos),deriv(deriv(pos)),deriv(deriv(deriv(pos))),deriv(deriv(deriv(deriv(pos))))
assert vp == [F(1),F(0),F(0),F(-10),F(15),F(-6)]
assert ap == [F(0),F(0),F(-30),F(60),F(-30)]
assert jp == [F(0),F(-60),F(180),F(-120)]
assert sp == [F(-60),F(360),F(-360)]
# Exact identity behind the whole-interval jerk bound, in z=y*(1-y).
def mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for k,b in enumerate(q): out[i+k]+=a*b
    return out
assert mul(mul([F(-1,6),F(1)],[F(-1,6),F(1)]),[F(1,3),F(4)]) == [F(1,108),F(0),F(-1),F(4)]
assert ev(pos,F(1)) == F(1,2)
assert [ev(p,F(0)) for p in [vp,ap,jp]] == [1,0,0]
assert [ev(p,F(1)) for p in [vp,ap,jp]] == [0,0,0]

result = {
 "status":"exact kinematic checks passed; no controller or hardware acceptance",
 "old_task_rejection": {"start":old_start,"requested_endpoint":old_endpoint[:3],
  "old_duration":F(1,4),"earliest_acceleration_zero":Tzero,
  "componentwise_lower_endpoint_at_earliest_zero":zero_endpoint,
  "position_excess":zero_endpoint[0]-old_endpoint[0],
  "velocity_excess":zero_endpoint[1]-old_endpoint[1],
  "necessary_zero_time_with_5ms_latency_after_arrival":a0/J+2*latency+2*J/S},
 "fixed_stop_task": {"arrival":arrival,"latency":latency,"deadline":deadline,
  "goal_position":X,"goal_velocity":0,"goal_acceleration":0,"goal_jerk":0,
  "reference_limits":{"position_min":0,"position_max":X,"velocity_min":0,
    "velocity_max":1,"absolute_acceleration":3,"absolute_jerk":J,"absolute_snap":S},
  "constant_snap_phases":phases,"blend_end_time":blend_end_time,"blend_end":blend_end,
  "cruise_duration":cruise,"brake_start":brake_start,"brake_start_state":q_brake,
  "brake_duration":L,"stop_time":stop_time,"hold_duration":deadline-stop_time,
  "exact_bounds":{"velocity_max":V,"blend_acceleration_max":blend_a_bound,
    "brake_absolute_acceleration_max":brake_a_bound,
    "brake_jerk_squared_max":brake_j_squared_bound,"brake_absolute_snap_max":brake_snap_bound},
  "brake_normalized_position_coefficients":pos},
 "scope":"Exact rational arithmetic plus stated polynomial-extrema arguments. The script alone does not prove the general admission theorem or real closed-loop safety."
}
(ROOT/'exact-task-check.json').write_text(json.dumps(data(result),indent=2)+'\n')
print(json.dumps(data({"checks":"passed","stop_time":stop_time,"deadline_slack":deadline-stop_time,"old_earliest_zero":Tzero}),indent=2))
