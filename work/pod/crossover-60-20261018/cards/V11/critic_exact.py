"""Independent exact scalar misuse/robust-envelope controls; no statistical inference from algebra."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).parent
# Precise biased observation passes a 3-sigma innovation gate, but the reported
# posterior 'covariance' cannot be an actual deterministic error certificate.
P, R, mu, x, z = F(1), F(1, 10**6), F(0), F(0), F(1, 10)
g = P / (P + R)
post_mu = mu + g * (z - mu)
post_P = P * R / (P + R)
assert (z - mu) ** 2 <= 9 * (P + R)
assert (post_mu - x) ** 2 > 9 * post_P and abs(post_mu - x) > abs(mu - x)
# Exact independent four-outcome distribution: truth X and common noise B each ±1.
# Repeat the SAME reading X+B. Noise remains unbiased, but records are correlated.
repeat = []
for N in [1, 2, 3, 10, 100]:
    errors = []
    for X in [F(-1), F(1)]:
        for B in [F(-1), F(1)]:
            Z = X + B
            mean = F(0)
            covariance = F(1)
            for _ in range(N):
                assert (Z - mean) ** 2 <= 9 * (covariance + 1)
                gain = covariance / (covariance + 1)
                mean += gain * (Z - mean)
                covariance = covariance / (covariance + 1)
            errors.append(mean - X)
    assert sum(errors) == 0
    actual = sum(e * e for e in errors) / 4
    assert actual == F(1 + N * N, (N + 1) ** 2)
    assert covariance == F(1, N + 1)
    assert actual == covariance if N == 1 else actual > covariance
    repeat.append(
        {"copies": N, "reported_variance": str(covariance), "actual_error_variance": str(actual)}
    )
# Parent's moving biased observations: normalized innovations stay below1.
mean = F(0)
covariance = F(1)
poison = []
for n in range(1, 11):
    Z = mean + 1
    innovation = Z - mean
    normalized = innovation**2 / (1 + covariance)
    assert normalized < 1
    gain = covariance / (1 + covariance)
    mean += gain * innovation
    covariance = covariance / (1 + covariance)
    assert mean == sum((F(1, k) for k in range(2, n + 2)), F(0))
    assert covariance == F(1, n + 1)
    poison.append(
        {
            "n": n,
            "mean": str(mean),
            "variance": str(covariance),
            "normalized_innovation_squared": str(normalized),
        }
    )
assert F(poison[2]["mean"]) == F(13, 12) > 1
# Existential geometric compatibility does not imply the true state survived intersection.
a, b, mu, x, z, g = F(1), F(1, 10), F(0), F(-1), F(21, 20), F(100, 101)
assert abs(z - mu) <= a + b and abs(x - mu) <= a
assert abs(z - x) > b
posterior = mu + g * (z - mu)
assert abs(posterior - x) == F(206, 101) > a
# Reusing a VALID bounded-error measurement does not shrink its feasible interval.
prior = (F(-1), F(1))
measurement = (F(1, 5), F(2, 5))
intersection = (max(prior[0], measurement[0]), min(prior[1], measurement[1]))
assert intersection == (F(1, 5), F(2, 5))
for _ in range(100):
    new = (max(intersection[0], measurement[0]), min(intersection[1], measurement[1]))
    assert new == intersection
# Generic ring inverse identities can hold for a negative 'covariance'.
P, R, U, V = F(1), F(1), F(1), F(-2)
S = R + V * P * U
Y = 1 / P + U * (1 / R) * V
Pc = P - P * U * (1 / S) * V * P
assert Y * Pc == 1 and Pc == -1
# Sharp worst-case error over interval [L,U] is max distance to endpoints.
# This requires actual truth membership, not only nonempty intersection.
endpoint_checks = 0
for L, U in [(F(-1), F(1)), (F(1, 5), F(2, 5))]:
    for candidate in [F(-2), F(0), F(1, 3), F(1), F(2)]:
        radius = max(abs(candidate - L), abs(candidate - U))
        for k in range(101):
            truth = L + (U - L) * F(k, 100)
            assert abs(candidate - truth) <= radius
            endpoint_checks += 1
out = {
    "precise_bias": {
        "posterior_mean": str(post_mu),
        "reported_variance": str(post_P),
        "passes_three_sigma_innovation_gate": True,
        "actual_error_squared_exceeds_nine_P": True,
    },
    "repeated_common_noise": repeat,
    "sequential_poisoning": poison,
    "geometric_compatibility_false_inlier_error": "206/101",
    "repeated_valid_set_intersection": list(map(str, intersection)),
    "ring_negative_covariance": "-1",
    "endpoint_checks": endpoint_checks,
    "scope": "Exact Fraction examples. Bias/poison cases violate valid-noise assumptions; repeated-noise case is unbiased but correlated. None refutes the source inverse identities. Endpoint truth-membership remains an explicit assumption.",
}
(HERE / "critic_exact.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
