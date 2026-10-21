"""Independent exact post-selection moments, without producer imports."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

worlds = list(product([F(-1), F(1)], repeat=2))
accepted = [(e, v) for e, v in worlds if v - e == 0]
assert len(worlds) == 4 and len(accepted) == 2


def moments(rows):
    posterior = [(e + v) / 2 for e, v in rows]
    mean = sum(posterior) / len(rows)
    return {
        "mean_error": str(mean),
        "error_variance": str(sum((p - mean) ** 2 for p in posterior) / len(rows)),
        "cross_moment": str(sum(e * v for e, v in rows) / len(rows)),
    }


a, b = moments(worlds), moments(accepted)
assert a["error_variance"] == "1/2" and a["cross_moment"] == "0"
assert b["error_variance"] == "1" and b["cross_moment"] == "1"
Path(__file__).with_suffix(".json").write_text(
    json.dumps(
        {
            "unconditional": a,
            "residual_zero_accepted": b,
            "scope": "Finite Rademacher product law; conditioning creates correlation. No claim of Gaussian conditional covariance failure.",
        },
        indent=2,
    )
    + "\n"
)
print(a, b)
