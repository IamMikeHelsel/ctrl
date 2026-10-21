"""Exact independent camera-domain negative controls; no producer imports."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def camera(point, center):
    return tuple(a - b for a, b in zip(point, center, strict=True))


def residual_sq(y, observation=(F(0), F(0))):
    assert y[2] != 0
    return sum((y[i] / y[2] - observation[i]) ** 2 for i in (0, 1))


def cone(y, gamma, observation=(F(0), F(0)), strict=True):
    return (y[2] > 0 if strict else y[2] >= 0) and sum(
        (y[i] - observation[i] * y[2]) ** 2 for i in (0, 1)
    ) <= gamma**2 * y[2] ** 2


def main():
    centers = [(F(0), F(0), F(0)), (F(1), F(0), F(0))]
    rows = []
    for gamma in (F(1), F(1, 10), F(1, 1000), F(1, 10**9)):
        point = (F(1, 2), F(0), 1 / (2 * gamma))
        assert all(cone(camera(point, c), gamma) for c in centers)
        assert all(residual_sq(camera(point, c)) == gamma**2 for c in centers)
        rows.append({"gamma": str(gamma), "point": list(map(str, point))})
    # gamma=0 implies x=0 and x-1=0, impossible; homogeneous point at infinity
    # (0,0,1,0) satisfies both homogenized zero-error rows but is not a finite point.
    assert all(F(0) - c[0] * F(0) == 0 for c in centers)
    assert not cone((F(0), F(0), F(0)), F(0))
    assert cone((F(0), F(0), F(0)), F(0), strict=False)
    behind = (F(0), F(0), F(-1))
    assert residual_sq(behind) == 0 and not cone(behind, F(0))
    assert sum(x * x for x in behind[:2]) <= F(0) ** 2 * behind[2] ** 2
    epigraph = [(F(1), F(1), F(1)), (F(9), F(3), F(3))]
    assert all(x / z <= gamma for x, z, gamma in epigraph)
    midpoint = tuple(sum(v) / 2 for v in zip(*epigraph, strict=True))
    assert midpoint[0] / midpoint[1] == F(5, 2) > midpoint[2]
    # Proper rotations I and diag(-1,1,-1); midpoint loses orthogonality.
    ra = (1, 1, 1)
    rb = (-1, 1, -1)
    assert ra[0] * ra[1] * ra[2] == rb[0] * rb[1] * rb[2] == 1
    rm = tuple(F(a + b, 2) for a, b in zip(ra, rb, strict=True))
    assert rm == (0, 1, 0) and rm[0] ** 2 != 1
    # Both valid endpoint pairs map their points to camera e3; independent
    # variable averaging destroys depth and cannot be licensed as convexity.
    xa, xb = (0, 0, 1), (0, 0, -1)
    assert tuple(a * b for a, b in zip(ra, xa, strict=True)) == (0, 0, 1)
    assert tuple(a * b for a, b in zip(rb, xb, strict=True)) == (0, 0, 1)
    # Pixel rectangle is not the Euclidean reprojection ball.
    assert max(abs(F(1)), abs(F(1))) <= 1 and F(1) ** 2 + F(1) ** 2 > 1
    # Depth normalization is not free when the metric baseline is fixed.
    p = (F(1, 2), F(0), F(1))
    assert residual_sq(camera(p, centers[1])) == F(1, 4)
    assert residual_sq(camera(tuple(2 * x for x in p), centers[1])) == 0
    # Valid Cayley rotations: the chart midpoint remains SO(3), unlike matrix averaging.
    chart = []
    for q in (F(-1, 2), F(1, 2)):
        c, s = (1 - q * q) / (1 + q * q), 2 * q / (1 + q * q)
        assert c * c + s * s == 1
        t = (-c, -s, F(1))
        y = (c + t[0], s + t[1], t[2])
        assert y == (0, 0, 1) and cone(y, F(1, 10))
        chart.append({"q": str(q), "translation": list(map(str, t))})
    midpoint_camera = (F(2, 5), F(0), F(1))
    assert not cone(midpoint_camera, F(1, 10))
    data = {
        "valid_rotation_chart_endpoints": chart,
        "valid_rotation_chart_midpoint_error": "2/5 > 1/10 at depth1",
        "arbitrarily_small_positive_threshold_witnesses": rows,
        "zero_threshold": "infeasible for finite positive-depth point; x=0 and x=1 conflict",
        "homogeneous_infinity": "(0,0,1,0) passes closure but is not finite",
        "zero_depth": "closed squared cone accepts origin; strict depth rejects",
        "behind_camera": "squared constraints and raw reprojection accept; positive depth rejects",
        "variable_threshold_epigraph_midpoint": list(map(str, midpoint)),
        "rotation_midpoint": list(map(str, rm)),
        "pixel_norm_mutation": "coordinatewise unit box accepts residual(1,1), Euclidean unit ball rejects",
        "metric_gauge_mutation": "scaling point without fixed camera baseline changes projection",
        "scope": "Exact rational fixtures; no solver status, numerical tolerance, or full rotation search.",
    }
    (HERE / "critic_boundaries.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
