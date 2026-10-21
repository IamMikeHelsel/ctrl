"""Exact scalar admission fixtures; hard radii are separate from covariance weights."""

import json
from fractions import Fraction as F
from pathlib import Path


def fixture(name, mu, radius, z, noise_bound, p, r, truth, target):
    mu, radius, z, noise_bound, p, r, truth, target = map(
        F, (mu, radius, z, noise_bound, p, r, truth, target)
    )
    assert p > 0 and r > 0
    mean = (mu / p + z / r) / (1 / p + 1 / r)
    gain_mean = mu + p / (p + r) * (z - mu)
    covariance = 1 / (1 / p + 1 / r)
    assert mean == gain_mean
    assert covariance == p * r / (p + r)
    lower, upper = max(mu - radius, z - noise_bound), min(mu + radius, z + noise_bound)
    compatible = lower <= upper
    actual_prior_valid = abs(truth - mu) <= radius
    actual_measurement_valid = abs(truth - z) <= noise_bound
    sharp_radius = max(abs(lower - mean), abs(upper - mean)) if compatible else None
    gate = compatible and mean - target <= lower and upper <= mean + target
    assert gate == (compatible and sharp_radius <= target)
    if actual_prior_valid and actual_measurement_valid:
        assert lower <= truth <= upper
        assert abs(truth - mean) <= sharp_radius
        if gate:
            assert abs(truth - mean) <= target
    return {
        "name": name,
        "prior_valid": actual_prior_valid,
        "measurement_valid": actual_measurement_valid,
        "interval_compatible": compatible,
        "mean": str(mean),
        "covariance": str(covariance),
        "actual_error": str(abs(truth - mean)),
        "actual_error_squared_le_covariance": (truth - mean) ** 2 <= covariance,
        "feasible_interval": [str(lower), str(upper)],
        "sharp_hard_radius": str(sharp_radius),
        "target": str(target),
        "admitted": gate,
    }


rows = [
    fixture("compatible_outlier", 0, 1, "21/20", "1/10", 1, "1/100", -1, 1),
    fixture("valid_bounds_covariance_failure", 0, 1, "1/2", "1/10", 1, "1/100", "3/5", "1/10"),
    fixture("valid_bounds_sharp_admission", 0, 1, "1/2", "1/10", 1, "1/100", "3/5", "53/505"),
    fixture("empty_intersection", 0, 1, 2, "1/10", 1, "1/100", 0, 1),
    fixture(
        "zero_innovation_still_not_truth_certification", 0, 1, 0, "1/10", 1, "1/100", 1, "1/10"
    ),
    fixture("exact_sensor_sound_limit", 0, 1, "1/2", 0, 1, "1/100", "1/2", "1/202"),
]
assert rows[0]["admitted"] and not rows[0]["measurement_valid"]
assert not rows[1]["admitted"] and rows[1]["measurement_valid"]
assert rows[2]["admitted"] and rows[2]["measurement_valid"]
assert not rows[3]["admitted"]
assert rows[4]["admitted"] and not rows[4]["measurement_valid"]
assert rows[5]["admitted"]

# Exact finite grid checks of the universal interval gate against its endpoint definition.
checks = 0
for lower in map(F, range(-3, 4)):
    for upper in map(F, range(-3, 4)):
        if lower > upper:
            continue
        for center in (F(i, 2) for i in range(-8, 9)):
            for target in (F(i, 2) for i in range(9)):
                gate = center - target <= lower and upper <= center + target
                endpoint_test = max(abs(lower - center), abs(upper - center)) <= target
                assert gate == endpoint_test
                checks += 1
out = {"arithmetic": "fractions.Fraction", "fixtures": rows, "finite_grid_checks": checks}
Path(__file__).with_name("domain_exact_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
