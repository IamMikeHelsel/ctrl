"""Exact adaptive-outlier witness; innovation acceptance is not noise certification."""

import json
from fractions import Fraction as F
from pathlib import Path

truth = F(0)
mean = F(0)
precision = F(1)
information = F(0)
rows = []
for n in range(1, 21):
    prior_variance = 1 / precision
    observation = mean + 1
    innovation = observation - mean
    normalized_squared = innovation**2 / (prior_variance + 1)
    assert normalized_squared < 1
    precision += 1
    information += observation
    mean = information / precision
    expected = sum((F(1, j) for j in range(2, n + 2)), F(0))
    assert mean == expected
    assert 1 / precision == F(1, n + 1)
    rows.append(
        {
            "n": n,
            "observation": str(observation),
            "innovation": str(innovation),
            "normalized_squared": str(normalized_squared),
            "mean": str(mean),
            "reported_variance": str(1 / precision),
            "actual_error": str(abs(mean - truth)),
        }
    )
assert rows[2]["mean"] == "13/12"
assert F(rows[2]["actual_error"]) > 1
result = {
    "prior": {"mean": "0", "variance": "1", "truth": "0", "certified_radius": "1"},
    "sensor_reported_variance": "1",
    "gate": "innovation_squared/(prior_variance+sensor_variance)<1",
    "rows": rows,
    "scope": "Adaptive arbitrary biased observations. All innovation gates pass; no true sensor bound or independence is assumed. Exact finite witness, not a valid-noise counterexample.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print("20 exact additive-information updates pass gate; at3 actual error13/12>prior radius1")
