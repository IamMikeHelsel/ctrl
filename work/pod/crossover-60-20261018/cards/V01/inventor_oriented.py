"""Exact declared calibrated-camera fixtures; no physical experiment or novelty claim."""

import json
from fractions import Fraction as F
from pathlib import Path


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def mv(a, x):
    return tuple(dot(row, x) for row in a)


def trans(a):
    return tuple(zip(*a, strict=True))


def mm(a, b):
    return tuple(tuple(dot(row, col) for col in trans(b)) for row in a)


def det(a):
    return sum(
        a[0][i] * (a[1][(i + 1) % 3] * a[2][(i + 2) % 3] - a[1][(i + 2) % 3] * a[2][(i + 1) % 3])
        for i in range(3)
    )


def image(x):
    assert x[2] != 0
    return tuple(a / x[2] for a in x)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def plane_h(r, t, n, distance):
    return tuple(tuple(r[i][j] + t[i] * n[j] / distance for j in range(3)) for i in range(3))


I = ((F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1)))
R_pi = ((F(-1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(-1)))
R_quarter = ((F(0), F(0), F(1)), (F(0), F(1), F(0)), (F(-1), F(0), F(0)))
for r in [R_pi, R_quarter]:
    assert mm(trans(r), r) == I
    assert det(r) == 1

# Duality negative with visible plane translation: H is not orthogonal.
shear = ((F(1), F(0), F(1)), (F(0), F(1), F(0)), (F(0), F(0), F(1)))
shear_inv = ((F(1), F(0), F(-1)), (F(0), F(1), F(0)), (F(0), F(0), F(1)))
line0, point0 = (F(1), F(0), F(0)), (F(0), F(1), F(1))
assert mm(shear_inv, shear) == I
point1 = mv(shear, point0)
line1, wrong_line1 = mv(trans(shear_inv), line0), mv(shear, line0)
assert dot(line0, point0) == dot(line1, point1) == 0
assert dot(wrong_line1, point1) == 1
assert point0[2] > 0 and point1[2] > 0

p = (F(1, 2), F(0), F(1))
behind = mv(R_pi, p)
assert behind == tuple(-a for a in p)
assert image(behind) == image(p)
assert p[2] > 0 > behind[2]

# An estimated homography's representative sign is not physical cheirality.
visible_ray = (F(-1, 5), F(0), F(1))
physical_target = mv(R_quarter, visible_ray)
alpha = F(-3)
estimated_h = tuple(tuple(alpha * a for a in row) for row in R_quarter)
estimated_target = mv(estimated_h, visible_ray)
assert image(physical_target) == image(estimated_target)
assert physical_target[2] > 0 > estimated_target[2]
assert estimated_target[2] / alpha == physical_target[2]

# Plane Z=1, t=0, d=1: source H=R exactly.
horizon_rows = []
for u in [F(-1, 10), F(-1, 1000), F(0), F(1, 1000), F(1, 10)]:
    x = (u, F(2, 3), F(1))
    y = mv(R_quarter, x)
    assert y == (F(1), F(2, 3), -u)
    assert y != (0, 0, 0)
    horizon_rows.append(
        {
            "source": x,
            "target_ray": y,
            "target_positive_depth": y[2] > 0,
            "standard_chart": image(y) if y[2] else None,
            "alternative_first_coordinate_chart": tuple(a / y[0] for a in y),
        }
    )

# Cotangent/adjoint transport is exact, but line inequalities need orientation.
delta = F(1, 10)
line = (F(-1), F(0), -delta)
line_target = mv(R_quarter, line)  # H^-T = H for this proper rotation.
assert line_target == (-delta, F(0), F(1))
guard_rows = []
for u in [F(-1, 5), F(-1, 10), F(-1, 20), F(1, 10)]:
    x = (u, F(0), F(1))
    y = mv(R_quarter, x)
    assert dot(line, x) == dot(line_target, y)
    target_affine = image(y)
    guard_rows.append(
        {
            "u": u,
            "original_guard": dot(line, x) >= 0,
            "homogeneous_transported_guard": dot(line_target, y) >= 0,
            "normalized_transported_guard": dot(line_target, target_affine) >= 0,
            "positive_depth": y[2] > 0,
        }
    )
assert guard_rows[-1]["original_guard"] is False
assert guard_rows[-1]["normalized_transported_guard"] is True

# Nonzero denominator alone supplies no uniform sensitivity bound.
conditioning = []
for n in [10, 100, 1000]:
    u, other = F(-1, n), F(-2, n)
    gain = abs(-1 / u + 1 / other) / abs(u - other)
    assert gain == F(n * n, 2)
    conditioning.append({"n": n, "source_distance": abs(u - other), "gain": gain})

# Exact rational probes of an independently derived depth-margin bound.
for u in [F(-1, 10), F(-1, 5), F(-1)]:
    for other in [F(-11, 100), F(-1, 2), F(-2)]:
        for v in [F(-2), F(0), F(2)]:
            for other_v in [F(-2), F(1, 3), F(2)]:
                assert abs(-1 / u + 1 / other) <= abs(u - other) / delta**2
                assert abs(-v / u + other_v / other) <= (
                    abs(v - other_v) / delta + 2 * abs(u - other) / delta**2
                )

# Passive frame changes: transport normals, rays AND optical axes.
q1, q2 = R_quarter, R_pi
r, t, normal, distance = I, (F(1), F(2), F(3)), (F(0), F(0), F(1)), F(2)
x_world = (F(2), F(1), F(2))
y_world = add(mv(r, x_world), t)
h = plane_h(r, t, normal, distance)
r_prime = mm(mm(q2, r), trans(q1))
t_prime, normal_prime = mv(q2, t), mv(q1, normal)
h_prime = plane_h(r_prime, t_prime, normal_prime, distance)
x_prime, y_prime = mv(q1, x_world), mv(q2, y_world)
assert mm(trans(r_prime), r_prime) == I and det(r_prime) == 1
assert h_prime == mm(mm(q2, h), trans(q1))
assert dot(normal_prime, x_prime) == distance
assert mv(h_prime, x_prime) == y_prime == add(mv(r_prime, x_prime), t_prime)
optical_prime = mv(q1, normal)
target_optical_prime = mv(q2, normal)
assert x_prime[2] < 0 < dot(optical_prime, x_prime)
assert dot(optical_prime, x_prime) == dot(normal, x_world) == 2
assert dot(target_optical_prime, y_prime) == dot(normal, y_world) == 5
ray1_prime = tuple(a / 2 for a in x_prime)
ray2_prime = tuple(a / 5 for a in y_prime)
assert dot(optical_prime, ray1_prime) == dot(target_optical_prime, ray2_prime) == 1
assert mv(h_prime, tuple(2 * a for a in ray1_prime)) == tuple(5 * a for a in ray2_prime)
assert dot(normal, x_prime) != distance  # Forgetting to transport plane normal fails.
wrong_h = plane_h(r_prime, t_prime, normal, distance)
assert mv(wrong_h, x_prime) != y_prime
assert plane_h(r, t, tuple(7 * a for a in normal), 7 * distance) == h

result = {
    "semantics": "calibrated rays; plane Z=1; zero translation; proper rotations",
    "orientation": {"R": R_pi, "X": p, "RX": behind, "same_pixel": image(p)},
    "estimated_gauge": {
        "alpha": alpha,
        "physical_H": R_quarter,
        "estimated_H": estimated_h,
        "input_ray": visible_ray,
        "physical_target": physical_target,
        "estimated_target": estimated_target,
        "physical_depth_ratio": estimated_target[2] / alpha,
    },
    "dual_transport": {
        "H": shear,
        "H_inv": shear_inv,
        "point": point0,
        "line": line0,
        "image_point": point1,
        "correct_line": line1,
        "wrong_point_rule_line": wrong_line1,
        "correct_incidence": dot(line1, point1),
        "wrong_incidence": dot(wrong_line1, point1),
        "physical_parameters": "R=I,t=e1,n=e3,d=1; positive-depth plane Z=1",
    },
    "horizon_rotation": R_quarter,
    "horizon_rows": horizon_rows,
    "guard_rows": guard_rows,
    "conditioning": conditioning,
    "passive_frame": {
        "R": r,
        "t": t,
        "n": normal,
        "d": distance,
        "H": h,
        "Q1": q1,
        "Q2": q2,
        "R_prime": r_prime,
        "t_prime": t_prime,
        "n_prime": normal_prime,
        "H_prime": h_prime,
        "X": x_world,
        "X_prime": x_prime,
        "Y": y_world,
        "Y_prime": y_prime,
        "transported_optical_axis": optical_prime,
        "transported_target_optical_axis": target_optical_prime,
        "source_ray_in_passive_basis": ray1_prime,
        "target_ray_in_passive_basis": ray2_prime,
        "positive_source_and_target_depths": [2, 5],
        "physical_depth_unchanged": dot(optical_prime, x_prime),
        "wrong_third_coordinate_depth": x_prime[2],
        "wrong_untransported_plane_motion": mv(wrong_h, x_prime),
    },
    "falsifiers": [
        "Negative target depth can preserve normalized pixels.",
        "An invertible proper rotation can send a finite point to the standard-chart horizon.",
        "Normalizing a negative-depth ray reverses a transported halfspace inequality.",
        "Nonzero target depths alone do not give a uniform pixel sensitivity bound.",
    ],
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print("PASS: proper rotations, oriented rays, horizon/chart, guard polarity, sensitivity probes")
