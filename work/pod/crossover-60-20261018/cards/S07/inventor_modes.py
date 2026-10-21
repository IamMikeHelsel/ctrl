"""Exact source-bound active-box, held-mode and post-clamp disturbance tests."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]
center, radius = [F(0), F(1, 10), F(2, 5)], F(1, 200)


def energy(z):
    return sum((P[i][j] * z[i] * z[j] for i in range(3) for j in range(3)), F(0))


def request(z):
    return -z[0] - 3 * z[1] - 2 * z[2]


def clamp(u):
    return max(-F(1), min(F(1), u))


def det3(A):
    return (
        A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
        - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
        + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])
    )


assert P[0][0] > 0 and P[0][0] * P[1][1] - P[0][1] ** 2 > 0 and det3(P) > 0
assert energy(center) == F(16367, 5000)
rows = []
for signs in product([-1, 1], repeat=3):
    z = [c + s * radius for c, s in zip(center, signs, strict=True)]
    r = request(z)
    assert r < -1 and energy(z) < 12
    for w in [-F(1, 100), F(1, 100)]:
        held = clamp(r) + w
        t = F(1, 10)
        # Exact cancellation in the source model; exponential parameter is shared.
        future_request = r - t * (z[1] + z[2]) - held * (2 * t + t * t / 2)
        assert -1 < future_request < 1
        assert clamp(r) == -1
        assert clamp(future_request) != clamp(r)
        rows.append(
            {
                "z": list(map(str, z)),
                "energy": str(energy(z)),
                "initial_request": str(r),
                "w": str(w),
                "held_total": str(held),
                "request_at_1_10": str(future_request),
            }
        )
assert min(F(row["initial_request"]) for row in rows) == -F(113, 100)
assert max(F(row["initial_request"]) for row in rows) == -F(107, 100)
assert min(F(row["request_at_1_10"]) for row in rows) == -F(19561, 20000)
assert max(F(row["request_at_1_10"]) for row in rows) == -F(18239, 20000)
# Disturbance placement does not commute with the clamp.
r0 = request(center)
post = clamp(r0) - F(1, 100)
pre = clamp(r0 - F(1, 100))
assert (post, pre) == (-F(101, 100), -F(1))
# Nor can post-clamp forcing be represented by a multiplicative gain at zero.
assert clamp(F(0)) + F(1, 100) != F(0)
# An admissible nonzero equilibrium prevents claims of convergence to origin.
w = F(1, 100)
equilibrium = [w, F(0), F(0)]
assert clamp(request(equilibrium)) + w == 0
assert energy(equilibrium) == F(19, 25000) < 12
out = {
    "source_model": "xprime=v,vprime=a,aprime=-a+clamp(-x0-3v0-2a0)+w; sampled request and w held.",
    "P": [[str(x) for x in row] for row in P],
    "P_determinant": str(det3(P)),
    "active_box": {
        "center": list(map(str, center)),
        "radius_each_coordinate": str(radius),
        "max_vertex_energy": str(max(F(row["energy"]) for row in rows)),
        "region_bound": "12",
        "initial_request_range": ["-113/100", "-107/100"],
        "request_at_time_1_10_range": ["-19561/20000", "-18239/20000"],
        "continuum_reason": "Convex quadratic energy bounded by box vertices; request affine in state and held disturbance within this fixed clamp mode.",
    },
    "post_vs_pre_clamp": {"post": str(post), "pre": str(pre)},
    "nonzero_equilibrium": {
        "state": list(map(str, equilibrium)),
        "w": str(w),
        "energy": str(energy(equilibrium)),
    },
    "vertices_and_disturbance_endpoints": rows,
    "scope": "Exact algebra plus hand convexity binding. Region proof belongs to source; this is neither a larger invariant nor physical validation.",
}
(HERE / "inventor_modes.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {k: v for k, v in out.items() if k != "vertices_and_disturbance_endpoints"}, indent=2
    )
)

# The request quotient hides an actual physical-position mode.
k = [F(1), -F(1), F(1)]
other = [c + q / 2 for c, q in zip(center, k, strict=True)]
assert request(k) == 0 and k[1] + k[2] == 0
assert energy(k) == F(189, 50)
assert request(other) == request(center) and other[1] + other[2] == center[1] + center[2]
assert energy(other) == F(5553, 1250) < 12
# Open-loop matrix with common held input maps k to -k.
Ak = [k[1], k[2], -k[2]]
assert Ak == [-q for q in k]
out["quotient_hidden_mode"] = {
    "kernel": list(map(str, k)),
    "other_active_state": list(map(str, other)),
    "other_energy": str(energy(other)),
    "same_request": str(request(other)),
    "same_b_v_plus_a": str(other[1] + other[2]),
    "position_difference": "(1/2)exp(-t) for common input/disturbance and identical sampling",
    "scope": "Hand ODE/induction consequence of Ak=-k and request(k)=0; not a proof that quotient alone bounds physical travel.",
}
(HERE / "inventor_modes.json").write_text(json.dumps(out, indent=2) + "\n")

# Declared parameter-perturbation negative: lagrate2 is outside the source model.
# Same quotient initial data no longer gives the same quotient derivatives.
A2k = [k[1], k[2], -2 * k[2]]
assert request(A2k) == 2
assert A2k[1] + A2k[2] == -1
out["outside_model_lagrate2_negative"] = {
    "request_derivative_difference_for_half_kernel": "1",
    "b_derivative_difference_for_half_kernel": "-1/2",
    "scope": "Changed-model diagnostic only: normalized lagrate1 is necessary for this quotient.",
}
(HERE / "inventor_modes.json").write_text(json.dumps(out, indent=2) + "\n")
