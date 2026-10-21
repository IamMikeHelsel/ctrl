"""Exact physical near-degeneracy: two common calibrations and proper rational poses."""

import json
from fractions import Fraction as F
from pathlib import Path


def cs(t):
    return (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)


def points(c, s, focal, depth, view):
    out = []
    for x in map(F, [-1, 0, 1]):
        for y in map(F, [-1, 0, 1]):
            xx, yy, z = (
                (x, y, depth)
                if view == "front"
                else ((x, c * y, depth + s * y) if view == "x" else (c * x, y, depth - s * x))
            )
            assert z > 0
            out.append((F(320) + focal * xx / z, F(240) + focal * yy / z))
    return out


rows = []
for denominator in [10, 100, 1000, 10000]:
    t = F(1, denominator)
    c, s = cs(t)
    cp, sp = cs(3 * t)
    assert c * c + s * s == cp * cp + sp * sp == 1
    f = sp * c / (cp * s)
    assert f > 3
    per = []
    for view in ["front", "x", "y"]:
        p = points(c, s, F(1000), F(5), view)
        q = points(cp, sp, 1000 * f, 5 * f, view)
        err = max(
            abs(a - b) for p0, q0 in zip(p, q, strict=True) for a, b in zip(p0, q0, strict=True)
        )
        per.append(err)
    assert per[0] == 0
    # For these two distinct positive common intrinsics, all observations can be their midpoint.
    rows.append(
        {
            "t": str(t),
            "focal_ratio": str(f),
            "focal1": "1000",
            "focal2": str(1000 * f),
            "max_coordinate_pixel_difference": str(max(per)),
            "max_coordinate_pixel_difference_float": float(max(per)),
            "midpoint_noise_radius": str(max(per) / 2),
            "c": str(c),
            "s": str(s),
            "c2": str(cp),
            "s2": str(sp),
            "depth1": "5",
            "depth2": str(5 * f),
        }
    )
assert F(rows[2]["max_coordinate_pixel_difference"]) < F(33, 10000)
Path(__file__).with_suffix(".json").write_text(
    json.dumps(
        {
            "scope": "27 finite correspondences; exact rational SO3 poses, common pinholeK permodel, positive depth. No physical or statistical claim.",
            "rows": rows,
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(rows, indent=2))
