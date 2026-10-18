"""Check arithmetic in the dependency audit. This is not a BCL checker."""
from fractions import Fraction as Q
from pathlib import Path
import json

c = Q(2, 47)
r_low = Q(8, 47)
r_high = Q(49, 125)
g = lambda r: r / 2 - r * r
assert r_low / 4 == c
assert g(r_high) == Q(1323, 31250)
assert c - g(r_high) == Q(319, 1468750) > 0
assert 2 * r_high - Q(1, 2) == Q(71, 250) > 0
assert Q(2, 5) - 2 * Q(1, 10**8) > r_high
assert c - Q(1, 25) == Q(3, 1175)
assert 47 * Q(1, 94) == Q(1, 2)

# Coefficients in [n^2, n*k, k^2, n, k, 1].
# choose(n-k,2) + k*n-k*(k+1)/2 = choose(n,2).
nonroot = [Q(1, 2), -1, Q(1, 2), Q(-1, 2), Q(1, 2), 0]
incident = [0, 1, Q(-1, 2), 0, Q(-1, 2), 0]
all_pairs = [Q(1, 2), 0, 0, Q(-1, 2), 0, 0]
assert [a + b for a, b in zip(nonroot, incident)] == all_pairs

# g(a)-g(r) = (r-a)*(r+a-1/2); coefficients in [r^2,r,1].
left = [Q(1), Q(-1, 2), g(r_high)]
right = [Q(1), Q(-1, 2), -r_high*r_high + r_high/2]
assert left == right

result = {
    "status": "pass",
    "scope": "Exact arithmetic for audit-derived branch and interface identities only",
    "is_bcl_certificate_check": False,
    "low_density_r": str(r_low),
    "low_density_cost": str(c),
    "high_density_r": str(r_high),
    "high_density_cost": str(g(r_high)),
    "high_density_slack": str(c-g(r_high)),
    "monotonic_factor_lower_bound": str(2*r_high-Q(1,2)),
    "stronger_bound_slack": str(c-Q(1,25)),
    "root_incident_edge_count": "k*n-k*(k+1)/2",
    "integer_gap_epsilon": "1/(94*n^2)",
    "integer_gap_after_multiplying_by_47": "1/2",
    "finite_sum_and_monotonicity_polynomial_coefficients_match": True,
}
Path(__file__).with_name("arithmetic-check.json").write_text(
    json.dumps(result, indent=2) + "\n"
)
print(json.dumps(result, indent=2))
