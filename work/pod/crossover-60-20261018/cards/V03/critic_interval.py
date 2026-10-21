"""Independent integer enumeration of all13 uncertain-coordinate box vertices."""

import copy
import json
from fractions import Fraction as F
from itertools import product
from math import lcm
from pathlib import Path

BASE = Path(__file__).parent
DATA = json.loads((BASE / "pm_interval.json").read_text())
CENTER = [[F(0), F(-2), F(0)], [F(2), F(0), F(1)], [F(0), F(1), F(0)]]


def extremum(depth, v, eps, eta, scale=F(1)):
    # Use one integer common denominator for x, one for y, one for E.
    xc = [F(0), v, F(1)]
    yc = [1 / depth, v, F(1)]
    xl = [xc[i] - eps if i < 2 else F(1) for i in range(3)]
    xu = [xc[i] + eps if i < 2 else F(1) for i in range(3)]
    yl = [yc[i] - eps if i < 2 else F(1) for i in range(3)]
    yu = [yc[i] + eps if i < 2 else F(1) for i in range(3)]
    el = [scale * z - eta for row in CENTER for z in row]
    eu = [scale * z + eta for row in CENTER for z in row]
    dx = lcm(*(z.denominator for z in xl + xu))
    dy = lcm(*(z.denominator for z in yl + yu))
    de = lcm(*(z.denominator for z in el + eu))
    xends = [(int(dx * a), int(dx * b)) for a, b in zip(xl, xu, strict=True)]
    yends = [(int(dy * a), int(dy * b)) for a, b in zip(yl, yu, strict=True)]
    eends = [(int(de * a), int(de * b)) for a, b in zip(el, eu, strict=True)]
    lower = upper = None
    count = 0
    for bits in product((0, 1), repeat=13):
        x = [xends[0][bits[9]], xends[1][bits[10]], dx]
        y = [yends[0][bits[11]], yends[1][bits[12]], dy]
        e = [eends[i][bits[i]] for i in range(9)]
        value = sum(y[i] * e[3 * i + j] * x[j] for i in range(3) for j in range(3))
        lower = value if lower is None else min(lower, value)
        upper = value if upper is None else max(upper, value)
        count += 1
    return F(lower, dx * dy * de), F(upper, dx * dy * de), count


def verify(data):
    counts = []
    eps, eta = F(data["coordinate_error"]), F(data["matrix_entry_error"])
    for row in data["cases"]:
        lo, hi, count = extremum(F(row["depth"]), F(row["v"]), eps, eta)
        if (lo, hi) != (F(row["lower"]), F(row["upper"])):
            raise ValueError("enclosure mismatch")
        if (lo > 0 or hi < 0) != row["reject_entire_candidate_box"]:
            raise ValueError("rejection mismatch")
        counts.append(count)
    return counts


counts = verify(DATA)
negatives = []
for mutation in ["lower_bound", "matrix_radius", "acceptance"]:
    bad = copy.deepcopy(DATA)
    if mutation == "lower_bound":
        bad["cases"][0]["lower"] = "1/3"
    elif mutation == "matrix_radius":
        bad["matrix_entry_error"] = "0"
    else:
        bad["cases"][1]["reject_entire_candidate_box"] = True
    try:
        verify(bad)
    except ValueError as error:
        negatives.append(dict(mutation=mutation, rejection=str(error)))
    else:
        raise ValueError("bad interval accepted")
lo, hi, _ = extremum(F(2), F(1, 3), F(1, 100), F(1, 100))
a, b, _ = extremum(F(2), F(1, 3), F(1, 100), F(3, 100), F(-3))
if (a, b) != (-3 * hi, -3 * lo):
    raise ValueError("registered scale covariance")
wrong = extremum(F(2), F(1, 3), F(1, 100), F(1, 100), F(-3))[:2]
if wrong == (a, b):
    raise ValueError("unscaled radius should change claim")
result = dict(
    vertices_per_case=counts,
    negative_controls=negatives,
    sign_scale_covariance_checked=True,
    unscaled_radius_changes_semantics=True,
    scope="Exact exhaustive vertex arithmetic plus hand multi-affine-extrema argument. E-entry box contains nonessential matrices, so exclusion is sound for its physical subset; zero inclusion is not physical compatibility. No full alternate-pose cover or Lean proof.",
)
(BASE / "critic_interval_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
