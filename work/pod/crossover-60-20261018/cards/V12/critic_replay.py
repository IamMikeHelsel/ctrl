"""Independent serialized rank-certificate and physical near-view audit."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_rank import design, rref

P = Path(__file__).parent


def parse(a):
    return [[F(x) for x in r] for r in a]


def mul(a, b):
    return [
        [sum(x * y for x, y in zip(r, c, strict=True)) for c in zip(*b, strict=True)] for r in a
    ]


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def check(c):
    hs = [parse(h) for h in c["H"]]
    a = parse(c["A"])
    u = parse(c["row_certificate"])
    v = parse(c["row_certificate_inverse"])
    rr = parse(c["rref"])
    assert a == design(hs)
    assert mul(u, a) == rr and mul(u, v) == mul(v, u) == eye(len(a))
    assert rref(a)[0] == rr and len(rref(a)[1]) == c["rank"]
    return c["rank"]


d = json.loads((P / "domain_rank.json").read_text())
ranks = [check(c) for c in d["cases"]]
k = parse(d["K"])
ki = parse(d["K_inverse"])
b = parse(d["B"])
assert mul(k, ki) == mul(ki, k) == eye(3)
assert mul(list(map(list, zip(*ki, strict=True))), ki) == b
physical_views = 0
for case in d["cases"]:
    for hs in case["H"]:
        extr = mul(ki, parse(hs))
        r1, r2, translation = map(list, zip(*extr, strict=True))
        r3 = [
            r1[1] * r2[2] - r1[2] * r2[1],
            r1[2] * r2[0] - r1[0] * r2[2],
            r1[0] * r2[1] - r1[1] * r2[0],
        ]
        R = list(map(list, zip(r1, r2, r3, strict=True)))
        assert mul(list(map(list, zip(*R, strict=True))), R) == eye(3)
        assert sum(x * y for x, y in zip(r3, r3, strict=True)) == 1
        assert (
            min(extr[2][0] * x + extr[2][1] * y + translation[2] for x in [-1, 1] for y in [-1, 1])
            > 0
        )
        physical_views += 1
mutations = []
for field in ["A", "rref", "row_certificate", "row_certificate_inverse", "H"]:
    c = json.loads(json.dumps(d["cases"][-1]))
    target = c[field]
    if field == "H":
        target = target[0]
    target[0][0] = str(F(target[0][0]) + 1)
    try:
        check(c)
    except AssertionError:
        mutations.append(field)
    else:
        raise AssertionError("accepted mutation " + field)
# Independently project homogeneous camera matrices, not producer's direct scalar projector.
near = []
for rec in json.loads((P / "pm_near_views.json").read_text())["rows"]:
    t = F(rec["t"])
    p = 3 * t
    c = (1 - t * t) / (1 + t * t)
    s = 2 * t / (1 + t * t)
    cp = (1 - p * p) / (1 + p * p)
    sp = 2 * p / (1 + p * p)
    f = 3 * (1 - t * t) / (1 - 9 * t * t)
    matrices = []
    pixels = []
    depthmins = []
    for cc, ss, ff in [(c, s, F(1)), (cp, sp, f)]:
        K = [[1000 * ff, 0, 320], [0, 1000 * ff, 240], [0, 0, 1]]
        rotations = [
            eye(3),
            [[1, 0, 0], [0, cc, -ss], [0, ss, cc]],
            [[cc, 0, ss], [0, 1, 0], [-ss, 0, cc]],
        ]
        hs = []
        ps = []
        zs = []
        for R in rotations:
            assert mul(list(map(list, zip(*R, strict=True))), R) == eye(3)
            # proper determinant of these explicitly axis-rotation matrices equals cc²+ss²=1.
            assert cc * cc + ss * ss == 1
            h = mul(K, [[R[i][0], R[i][1], 5 * ff if i == 2 else 0] for i in range(3)])
            hs.append(h)
            for x in [-1, 0, 1]:
                for y in [-1, 0, 1]:
                    z = [sum(a * b for a, b in zip(row, [x, y, 1], strict=True)) for row in h]
                    assert z[2] > 0
                    zs.append(z[2])
                    ps.append([z[0] / z[2], z[1] / z[2]])
        assert len(rref(design(hs))[1]) == 5
        matrices.append(hs)
        pixels.append(ps)
        depthmins.append(min(zs))
    err = max(abs(x - y) for a, b0 in zip(*pixels, strict=True) for x, y in zip(a, b0, strict=True))
    assert err == F(rec["max_coordinate_pixel_difference"])
    assert err / 2 == F(rec["midpoint_noise_radius"])
    near.append(
        {
            "t": str(t),
            "rank_each": 5,
            "max_error": str(err),
            "depth_minima": list(map(str, depthmins)),
        }
    )
out = {
    "rank_replays": ranks,
    "physical_domain_views_checked": physical_views,
    "matrix_mutations_rejected": mutations,
    "near_physical_models": near,
    "scope": "Exact rational finite 27-point data; coordinatewise midpoint noise bound, not statistical likelihood or all-board bound.",
}
(P / "critic_replay.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    "Independent rank and inverse-metric binding; five certificate corruptions; four physical ambiguity fixtures passed"
)
