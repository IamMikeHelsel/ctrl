"""Exact moving-frame optical-axis jets, through jerk; no actuator model."""

import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions required")

I = [[F(i == j) for j in range(3)] for i in range(3)]
O = [[F(0) for _ in range(3)] for _ in range(3)]
X = [[F(0), F(0), F(0)], [F(0), F(0), F(-1)], [F(0), F(1), F(0)]]
Y = [[F(0), F(0), F(1)], [F(0), F(0), F(0)], [F(-1), F(0), F(0)]]
Z = [[F(0), F(-1), F(0)], [F(1), F(0), F(0)], [F(0), F(0), F(0)]]


def ma(a, b):
    return [[a[i][j] + b[i][j] for j in range(3)] for i in range(3)]


def ms(c, a):
    return [[c * x for x in row] for row in a]


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def mv(a, v):
    return [sum(a[i][j] * v[j] for j in range(3)) for i in range(3)]


def tr(a):
    return [list(row) for row in zip(*a, strict=True)]


def va(a, b):
    return [x + y for x, y in zip(a, b, strict=True)]


def vs(c, a):
    return [c * x for x in a]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def power(a, n):
    out = I
    for _ in range(n):
        out = mm(out, a)
    return out


def pmm(a, b):
    out = [O for _ in range(4)]
    for k in range(4):
        for j in range(k + 1):
            out[k] = ma(out[k], mm(a[j], b[k - j]))
    return out


# Taylor coefficients of actual smooth rotations, not arbitrary matrix jets:
# R(t)=exp(t Z) exp(t² X/2); D(t)=exp(t Y) exp(2t Z); d(t)=D(t)e1.
rz = [ms(F(1, factorial(k)), power(Z, k)) for k in range(4)]
rx_quadratic = [I, O, ms(F(1, 2), X), O]
r = pmm(rz, rx_quadratic)
drot = pmm(
    [ms(F(1, factorial(k)), power(Y, k)) for k in range(4)],
    [ms(F(2**k, factorial(k)), power(Z, k)) for k in range(4)],
)
e1 = [F(1), F(0), F(0)]
d = [vs(F(factorial(k)), mv(drot[k], e1)) for k in range(4)]
p_matrix = pmm([tr(a) for a in r], drot)
p = [vs(F(factorial(k)), mv(p_matrix[k], e1)) for k in range(4)]
omega, omega_dot = Z, X
omega_ddot = ma(mm(Z, X), ms(-1, mm(X, Z)))
c, e, f = d[1], d[2], d[3]  # R(0)=I
p1 = va(c, vs(-1, mv(omega, p[0])))
p2 = va(va(e, vs(-2, mv(omega, c))), mv(ma(power(omega, 2), ms(-1, omega_dot)), p[0]))
last = ma(
    ma(ms(2, mm(omega_dot, omega)), mm(omega, omega_dot)),
    ma(ms(-1, omega_ddot), ms(-1, power(omega, 3))),
)
p3 = va(
    va(f, vs(-3, mv(omega, e))),
    va(vs(3, mv(ma(power(omega, 2), ms(-1, omega_dot)), c)), mv(last, p[0])),
)
assert p[1:] == [p1, p2, p3]
assert dot(p[0], p[0]) == 1
assert dot(p[0], p[1]) == 0
assert dot(p[1], p[1]) + dot(p[0], p[2]) == 0
assert 3 * dot(p[1], p[2]) + dot(p[0], p[3]) == 0
# Reconstruct all world jets by Leibniz from retained base and relative jets.
rjets = [ms(F(factorial(k)), r[k]) for k in range(4)]
for k in range(4):
    world = [F(0)] * 3
    for j in range(k + 1):
        world = va(world, vs(F(comb(k, j)), mv(rjets[j], p[k - j])))
    assert world == d[k]
# Deliberately omit the noncommuting omega_dot*omega contribution.
wrong_p3 = va(p3, vs(-2, mv(mm(omega_dot, omega), p[0])))
assert wrong_p3 != p3

# Stationary world ray while base rotates about z with unit speed.
stationary_p = [e1, [F(0), F(-1), F(0)], [F(-1), F(0), F(0)], [F(0), F(1), F(0)]]
wrong_world_acceleration = va(mv(power(Z, 2), e1), vs(2, mv(Z, stationary_p[1])))
assert wrong_world_acceleration == e1  # setting relative acceleration0 is wrong

# Constant passive coordinate relabel Q=90-degree z rotation.
Q = [[F(0), F(-1), F(0)], [F(1), F(0), F(0)], [F(0), F(0), F(1)]]
assert mm(tr(Q), Q) == I
new_p = [mv(tr(Q), jet) for jet in stationary_p]
new_omega = mm(mm(tr(Q), Z), Q)
correct_world_velocity = mv(Q, va(new_p[1], mv(new_omega, new_p[0])))
wrong_world_velocity = mv(Q, va(stationary_p[1], mv(new_omega, new_p[0])))
assert correct_world_velocity == [0, 0, 0]
assert wrong_world_velocity == [1, 1, 0]
# Authority: target direction and base rotation can each have unit speed.
co_moving = va([F(0), F(1), F(0)], vs(-1, mv(Z, e1)))
opposed = va([F(0), F(-1), F(0)], vs(-1, mv(Z, e1)))
assert dot(co_moving, co_moving) == 0
assert dot(opposed, opposed) == 4 > F(3, 2) ** 2
# A Euclidean interpolation of antipodal unit gaze goals crosses the origin;
# normalizing that retained reference is undefined at the midpoint.
antipodal_midpoint = vs(F(1, 2), va(e1, vs(-1, e1)))
assert antipodal_midpoint == [0, 0, 0]
# Coordinate derivative norms are not joint-angle acceleration/jerk:
# qyaw=-t has zero second/third derivatives but p=Rz(-t)e1 does not.
assert all(dot(jet, jet) == 1 for jet in stationary_p)

out = {
    "status": "pass",
    "units": "normalized angular kinematics",
    "base": "R=exp(tZ)exp(t²X/2)",
    "world_goal": "d=exp(tY)exp(2tZ)e1",
    "world_jets": [[str(x) for x in a] for a in d],
    "relative_jets": [[str(x) for x in a] for a in p],
    "reconstructed_world_derivatives_through_order": 3,
    "stationary_world_wrong_acceleration": list(map(str, wrong_world_acceleration)),
    "frame_relabel_wrong_world_velocity": list(map(str, wrong_world_velocity)),
    "opposed_required_relative_speed_squared": "4",
    "declared_relative_speed_cap": "3/2",
    "antipodal_Euclidean_goal_midpoint": [0, 0, 0],
    "metric_boundary": "constant yaw-joint rate has zero joint acceleration/jerk, "
    "but body-ray coordinate acceleration/jerk norm1",
    "boundary": "Exact finite jets of actual smooth rotation paths and hand product-rule "
    "identities. No joint inverse kinematics, gimbal singularity treatment, "
    "torque, sampled execution, or physical tracking theorem.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
