"""Independent full lifts, uniqueness of image rays, rank and noncoplanarity checks."""

import copy
import json
import runpy
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
lib = runpy.run_path(str(BASE / "critic_geometry.py"), run_name="critic_library")
dot, mv, mm, skew, rank, det = [lib[k] for k in ["dot", "mv", "mm", "skew", "rank", "det"]]
I = [[F(i == j) for j in range(3)] for i in range(3)]
DATA = json.loads((BASE / "inventor_exact.json").read_text())


def verify(data):
    scene = data["scene"] + data["noncolliding_offplane_examples"]
    rays1 = [tuple(map(F, p["x1"])) for p in scene]
    rays2 = [tuple(map(F, p["x2"])) for p in scene]
    if len(set(rays1)) != len(scene) or len(set(rays2)) != len(scene):
        raise ValueError("colliding image rays")
    output = []
    for pose, key in enumerate(["pose_A", "pose_B"]):
        R = [list(map(F, row)) for row in data[key]["R"]]
        t = list(map(F, data[key]["t"]))
        worlds = []
        for p, x, y in zip(scene, rays1, rays2, strict=True):
            if "depths_in_both_cameras" in p:
                d1 = d2 = F(p["depths_in_both_cameras"][pose])
            else:
                d1, d2 = map(F, p["depths_A" if pose == 0 else "depths_B"])
            X = [d1 * z for z in x]
            if min(d1, d2) <= 0 or [a + b for a, b in zip(mv(R, X), t, strict=True)] != [
                d2 * z for z in y
            ]:
                raise ValueError("physical lift")
            worlds.append(X)
        derivatives = [mm(skew(axis), R) for axis in I] + [
            mm(mm(skew(t), skew(axis)), R) for axis in I
        ]
        jac = [[dot(y, mv(de, x)) for de in derivatives] for x, y in zip(rays1, rays2, strict=True)]
        if rank(jac) != 5:
            raise ValueError("local rank")
        cert = data["augmented_fixture"]["noncoplanarity_A_B"][pose]
        points = [list(map(F, p)) for p in cert["four_world_points"]]
        if not all(p in worlds for p in points):
            raise ValueError("volume witness not a retained point")
        volume = det([[z - w for z, w in zip(p, points[0], strict=True)] for p in points[1:]])
        if not volume or volume != F(cert["affine_determinant"]):
            raise ValueError("noncoplanarity witness")
        output.append(dict(pose=key, points=len(worlds), rank=rank(jac), affine_volume=str(volume)))
    return output


verified = verify(DATA)
negatives = []
for kind in ["collision", "depth", "volume"]:
    bad = copy.deepcopy(DATA)
    if kind == "collision":
        bad["scene"].append(copy.deepcopy(bad["scene"][0]))
    elif kind == "depth":
        bad["noncolliding_offplane_examples"][0]["depths_B"][0] = "-1"
    else:
        bad["augmented_fixture"]["noncoplanarity_A_B"][0]["affine_determinant"] = "0"
    try:
        verify(bad)
    except ValueError as error:
        negatives.append(dict(mutation=kind, rejection=str(error)))
    else:
        raise ValueError("corruption accepted")
result = dict(
    cases=verified,
    negative_controls=negatives,
    scope="14 distinct image correspondences, both positive-depth reconstructions noncoplanar, both local ranks5. Concrete global ambiguity, not generic scene claim or opaque-surface validation.",
)
(BASE / "critic_augmented_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
