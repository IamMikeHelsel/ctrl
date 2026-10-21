"""Exact physical planar ambiguity and local epipolar differential ranks."""

import json
from fractions import Fraction as F
from pathlib import Path


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def transpose(a):
    return list(map(list, zip(*a, strict=True)))


def mul(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def mv(a, x):
    return [dot(row, x) for row in a]


def add(a, b):
    return [[x + y for x, y in zip(r, s, strict=True)] for r, s in zip(a, b, strict=True)]


def skew(x):
    a, b, c = x
    return [[0, -c, b], [c, 0, -a], [-b, a, 0]]


def det(a):
    return sum(
        a[0][i] * (a[1][(i + 1) % 3] * a[2][(i + 2) % 3] - a[1][(i + 2) % 3] * a[2][(i + 1) % 3])
        for i in range(3)
    )


def rref(a):
    a = [list(map(F, row)) for row in a]
    row = 0
    pivots = []
    for col in range(len(a[0])):
        pivot = next((j for j in range(row, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        scale = a[row][col]
        a[row] = [x / scale for x in a[row]]
        for j in range(len(a)):
            if j != row:
                scale = a[j][col]
                a[j] = [x - scale * y for x, y in zip(a[j], a[row], strict=True)]
        pivots.append(col)
        row += 1
        if row == len(a):
            break
    return pivots, a


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, list):
        return [encode(v) for v in x]
    if isinstance(x, dict):
        return {k: encode(v) for k, v in x.items()}
    return x


I = [[F(int(i == j)) for j in range(3)] for i in range(3)]
H = [[F(1), F(0), F(1)], [F(0), F(1), F(0)], [F(0), F(0), F(1)]]
R = [[F(3, 5), F(0), F(4, 5)], [F(0), F(1), F(0)], [F(-4, 5), F(0), F(3, 5)]]
t = [F(1), F(0), F(2)]
m = [F(2, 5), F(0), F(1, 5)]
assert mul(transpose(R), R) == I and det(R) == 1
assert add(R, [[x * y for y in m] for x in t]) == H
poses = [(I, [F(1), F(0), F(0)]), (R, t)]
Es = [mul(skew(ti), ri) for ri, ti in poses]
scene = []
for u in [F(-1, 4), F(0), F(1, 4), F(1, 2)]:
    for v in [F(-1, 3), F(0), F(1, 3)]:
        x = [u, v, F(1)]
        y = mv(H, x)
        depths = [F(1), F(5) / (2 * u + 1)]
        for (ri, ti), depth, e in zip(poses, depths, Es, strict=True):
            X = [depth * z for z in x]
            Y = [a + b for a, b in zip(mv(ri, X), ti, strict=True)]
            assert Y == [depth * z for z in y]
            assert depth > 0 and Y[2] > 0
            assert dot(y, mv(e, x)) == 0
        scene.append({"x1": x, "x2": y, "depths_in_both_cameras": depths})

# Differential chart: tx=1 fixes translation-scale gauge for both poses.
# Left rotation perturbation deltaR=[omega]R supplies all SO(3) tangent axes.
ranks = []
jacobians = []
for ri, ti in poses:
    dEs = [mul(mul(skew(ti), skew(axis)), ri) for axis in I]
    dEs += [mul(skew(axis), ri) for axis in I[1:]]
    jac = [[dot(p["x2"], mv(de, p["x1"])) for de in dEs] for p in scene]
    pivots, reduced = rref(jac)
    assert len(pivots) == 5
    ranks.append(len(pivots))
    jacobians.append(
        {
            "columns": ["omega_x", "omega_y", "omega_z", "delta_ty", "delta_tz"],
            "matrix": jac,
            "rref": reduced,
        }
    )
    full_dEs = [mul(skew(axis), ri) for axis in I]
    full_dEs += [mul(mul(skew(ti), skew(axis)), ri) for axis in I]
    full_jac = [[dot(p["x2"], mv(de, p["x1"])) for de in full_dEs] for p in scene]
    full_pivots, full_reduced = rref(full_jac)
    assert len(full_pivots) == 5
    scale_kernel = ti + [F(0)] * 3
    assert all(dot(row, scale_kernel) == 0 for row in full_jac)
    jacobians[-1]["full_six_columns"] = ["tx", "ty", "tz", "omega_x", "omega_y", "omega_z"]
    jacobians[-1]["full_six_matrix"] = full_jac
    jacobians[-1]["full_six_rref"] = full_reduced
    jacobians[-1]["full_six_rank"] = len(full_pivots)
    jacobians[-1]["scale_kernel"] = scale_kernel
    if ri == I:
        for p, row in zip(scene, full_jac, strict=True):
            u, v, _ = p["x1"]
            assert row == [0, 1, -v, -(v * v + 1), u * v, u]

# Deliberately non-planar extra observation under pose A, depth2.
# It rejects B only for transverse v!=0; off-plane alone is insufficient.
offplane = []
for v in [F(0), F(1, 3)]:
    x, y = [F(0), v, F(1)], [F(1, 2), v, F(1)]
    residuals = [dot(y, mv(e, x)) for e in Es]
    assert residuals == [F(0), v]
    offplane.append({"x1": x, "x2": y, "true_depth": 2, "residuals_A_B": residuals})

# Full-lift check matters: depth2,v0 above forces depth0 in B's first camera.
# Depth3/2 instead provides a genuine offplane positive-depth ambiguity.
critical_x = [F(0), F(0), F(1)]
critical_y = [F(2, 3), F(0), F(1)]
critical_depths = [[F(3, 2), F(3, 2)], [F(5, 6), F(5, 2)]]
for (ri, ti), (d1, d2) in zip(poses, critical_depths, strict=True):
    left = [d2 * value for value in critical_y]
    right = [a + b for a, b in zip(mv(ri, [d1 * value for value in critical_x]), ti, strict=True)]
    assert left == right and d1 > 0 and d2 > 0
assert critical_depths[0][0] != 1
critical_noncolliding = []
for X in [F(-1, 10), F(1, 10)]:
    Z = F(3, 2)
    x = [X / Z, F(0), F(1)]
    y = [(X + 1) / Z, F(0), F(1)]
    denominator = 4 * X * X + 4 * X + 4 * Z * Z - 3 * Z
    d1 = 5 * Z * (2 * X + 2 - Z) / denominator
    d2 = d1 * (F(-4, 5) * X / Z + F(3, 5)) + 2
    assert d1 > 0 and d2 > 0
    assert [d2 * value for value in y] == [
        a + b for a, b in zip(mv(R, [d1 * value for value in x]), t, strict=True)
    ]
    assert all(x != p["x1"] and y != p["x2"] for p in scene)
    critical_noncolliding.append(
        {"world_A": [X, F(0), Z], "x1": x, "x2": y, "depths_A": [Z, Z], "depths_B": [d1, d2]}
    )

augmented = scene + critical_noncolliding
assert len({tuple(p["x1"]) for p in augmented}) == len(augmented)
assert len({tuple(p["x2"]) for p in augmented}) == len(augmented)
augmented_ranks = []
noncoplanarity = []
for pose_id, (ri, ti) in enumerate(poses):
    dEs = [mul(skew(axis), ri) for axis in I]
    dEs += [mul(mul(skew(ti), skew(axis)), ri) for axis in I]
    jac = [[dot(p["x2"], mv(de, p["x1"])) for de in dEs] for p in augmented]
    rank = len(rref(jac)[0])
    assert rank == 5
    augmented_ranks.append(rank)
    plane_rays = [[F(-1, 4), F(-1, 3), F(1)], [F(1, 4), F(-1, 3), F(1)], [F(-1, 4), F(1, 3), F(1)]]
    lifted = []
    for ray in plane_rays:
        depth = F(1) if pose_id == 0 else F(5) / (2 * ray[0] + 1)
        lifted.append([depth * z for z in ray])
    extra = critical_noncolliding[1]
    extra_depth = extra["depths_A" if pose_id == 0 else "depths_B"][0]
    lifted.append([extra_depth * z for z in extra["x1"]])
    difference = [
        [value - base for value, base in zip(point, lifted[0], strict=True)] for point in lifted[1:]
    ]
    volume = det(difference)
    assert volume != 0
    noncoplanarity.append({"four_world_points": lifted, "affine_determinant": volume})

# Linear epipolar-matrix identifiability is a separate layer from the essential
# tangent rank. A final transverse offplane ray raises rank to8 in this fixture.
discriminating = {"x1": [F(0), F(1, 2), F(1)], "x2": [F(1, 2), F(1, 2), F(1)]}
assert all(discriminating["x1"] != p["x1"] and discriminating["x2"] != p["x2"] for p in augmented)
pure_rotation_cosines = []
for aa, bb in [
    ([F(0), F(0), F(1)], [F(0), F(1, 3), F(1)]),
    ([F(1), F(0), F(1)], [F(1), F(1, 3), F(1)]),
]:
    pure_rotation_cosines.append(dot(aa, bb) ** 2 / (dot(aa, aa) * dot(bb, bb)))
assert pure_rotation_cosines == [F(9, 10), F(18, 19)]
design_ranks = []
design_certificates = []
for label, records in [
    ("planar12", scene),
    ("critical_noncoplanar14", augmented),
    ("discriminated15", augmented + [discriminating]),
]:
    design = [[yi * xj for yi in p["x2"] for xj in p["x1"]] for p in records]
    pivots, reduced = rref(design)
    rank = len(pivots)
    flat_EA = [value for row in Es[0] for value in row]
    assert all(dot(row, flat_EA) == 0 for row in design)
    design_ranks.append(rank)
    design_certificates.append({"label": label, "matrix": design, "rref": reduced, "rank": rank})
assert design_ranks == [6, 7, 8]

# Pure rotation identity: valid essential matrices for arbitrary t fit the
# algebraic epipolar equations, yet t=e1 cannot triangulate ray e3 at finite depth.
x = [F(0), F(0), F(1)]
assert dot(x, mv(Es[0], x)) == 0
assert mv(I, x)[0] == 0 and poses[0][1][0] == 1
# First coordinate equation is 0=1 for any finite pair of depths.
pure_jac = []
for p in scene:
    x = p["x1"]
    pure_jac.append([F(0)] * 3 + [dot(x, mv(skew(axis), x)) for axis in I])
assert len(rref(pure_jac)[0]) == 0

# Bounded coordinate error: x/y first2 coordinates each vary independently by
# at most epsilon, homogeneous coordinates remain1. Exact triangle inequality
# for bilinear residual gives L*epsilon+4*epsilon^2 for this E_B.
noise_tests = []
epsilon = F(1, 100)
for Z in [F(2), F(101, 100)]:
    v = F(1, 3)
    x, y = [F(0), v, F(1)], [1 / Z, v, F(1)]
    residual = dot(y, mv(Es[1], x))
    assert residual == 2 * v * (Z - 1) / Z
    L = sum(abs(z) for z in mv(Es[1], x)[:2])
    L += sum(abs(z) for z in mv(transpose(Es[1]), y)[:2])
    error_bound = L * epsilon + 4 * epsilon * epsilon
    certified_reject = abs(residual) > error_bound
    assert certified_reject == (Z == 2)
    ambiguity = abs(F(1) - y[0]) <= epsilon
    assert ambiguity == (Z == F(101, 100))
    # In nearplane case, rounded second-ray coordinate1 is within noise budget
    # and is exactly the correspondence generated by both planar hypotheses.
    if ambiguity:
        y_round = [F(1), v, F(1)]
        assert dot(y_round, mv(Es[1], x)) == 0
    noise_tests.append(
        {
            "Z": Z,
            "epsilon_each_coordinate": epsilon,
            "candidate_B_residual": residual,
            "bilinear_error_bound": error_bound,
            "certified_reject": certified_reject,
            "can_round_to_exact_planar_correspondence": ambiguity,
        }
    )

result = {
    "model": "Calibrated normalized real pinhole rays, SO(3), finite strictly positive depths; unknown scene planes, metric translation scale unobservable.",
    "H": H,
    "pose_A": {"R": I, "t": poses[0][1], "plane": "z=1"},
    "pose_B": {"R": R, "t": t, "inverse_plane_vector": m},
    "essential_matrices": Es,
    "scene": scene,
    "all_correspondences_cheiral_under_both_distinct_poses": True,
    "scale_gauge_removed_local_epipolar_ranks": ranks,
    "jacobians": jacobians,
    "local_global_limit": "Full tangent rank at both exhibited solutions does not imply global uniqueness; no claim of complete solution enumeration.",
    "offplane_tests": offplane,
    "offplane_critical_direction_physical_ambiguity": {
        "x1": critical_x,
        "x2": critical_y,
        "depth_pairs_A_B": critical_depths,
        "full_rigid_equations_and_cheirality_checked": True,
        "contrast": "The depth2,v0 epipolar-only fixture instead has candidateB firstdepth0. Only this depth3/2 fixture establishes a physical ambiguity after adding an offplane point.",
    },
    "noncolliding_offplane_examples": critical_noncolliding,
    "augmented_fixture": {
        "unique_rays_both_cameras": True,
        "full_six_local_ranks_A_B": augmented_ranks,
        "noncoplanarity_A_B": noncoplanarity,
    },
    "linear_matrix_design": design_certificates,
    "linear_matrix_design_ranks": design_ranks,
    "discriminating_fifteenth_correspondence": discriminating,
    "pure_rotation_exclusion_squared_cosines": pure_rotation_cosines,
    "critical_variety_derivation": "For A-world(X,Y,Z), Z!=0, the B epipolar residual is2Y(Z-1)/Z^2. Its zero set is the union Y=0 or Z=1; cheirality must additionally be checked. Two tested offplane points have distinct rays from all original planar points in both cameras. No opaque surface or occlusion model is assumed.",
    "noise_margin_tests": noise_tests,
    "zero_baseline": {
        "true_E": [[0] * 3 for _ in range(3)],
        "epipolar_jacobian_rank": 0,
        "false_nonzero_translation_fit": "R=I,t=e1 fits x2=x1 epipolar algebra, but ray e3 requires impossible finite-depth equation0=1.",
    },
    "evidence": "Exact rational checks and explicit matrices; no kernel proof, noise robustness, novelty or physical validation claimed.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(
    json.dumps(
        {
            "physical_planar_solutions": 2,
            "local_ranks": ranks,
            "offplane_residuals": encode(offplane),
            "pure_rotation_epipolar_rank": 0,
        },
        indent=2,
    )
)
