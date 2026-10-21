"""Exact independent Rademacher errors: selection changes the covariance meaning."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

worlds = []
for prior_error, measurement_noise in itertools.product((-1, 1), repeat=2):
    worlds.append(
        {
            "prior_error": F(prior_error),
            "measurement_noise": F(measurement_noise),
            "innovation": F(measurement_noise - prior_error),
            "posterior_error": F(prior_error + measurement_noise, 2),
            "probability": F(1, 4),
        }
    )


def moments(rows, key):
    mass = sum(row["probability"] for row in rows)
    mean = sum(row["probability"] * row[key] for row in rows) / mass
    variance = sum(row["probability"] * (row[key] - mean) ** 2 for row in rows) / mass
    return mean, variance


assert moments(worlds, "prior_error") == (0, 1)
assert moments(worlds, "measurement_noise") == (0, 1)
assert (
    sum(row["probability"] * row["prior_error"] * row["measurement_noise"] for row in worlds) == 0
)
# All four Cartesian product outcomes have probability(1/2)*(1/2), so independence is exact.
assert moments(worlds, "posterior_error") == (0, F(1, 2))
accepted = [row for row in worlds if row["innovation"] == 0]
assert moments(accepted, "posterior_error") == (0, 1)
assert sum(row["probability"] for row in accepted) == F(1, 2)
out = {
    "law": "independent equiprobable +/-1 prior and measurement errors",
    "gate": "accept iff absolute innovation <= 0",
    "unconditional_posterior_variance": "1/2",
    "conditional_accepted_posterior_variance": "1",
    "acceptance_probability": "1/2",
    "information_formula": "(1/P+1/R)^(-1)=1/2",
    "worlds": [{key: str(value) for key, value in row.items()} for row in worlds],
    "scope": "Exact four-point distribution, not Gaussian; no contradiction of algebraic identity.",
}
Path(__file__).with_name("domain_selection_results.json").write_text(
    json.dumps(out, indent=2) + "\n"
)
print(json.dumps(out, indent=2))
