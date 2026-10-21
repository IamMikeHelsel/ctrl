"""Independent exact algebra supporting global direct-jerk bound and separation."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

BASE = Path(__file__).parent
# P is the dimensionless continuous impulse polynomial; R-exp primitive.
p = [F(3), F(-3), F(1, 2)]
r = [F(1), F(-2), F(1, 2)]
rprime = [r[1], 2 * r[2], F(0)]
if [a - b for a, b in zip(r, rprime, strict=True)] != p:
    raise ValueError("primitive identity")
# P=(x-(3-sqrt3))(x-(3+sqrt3))/2; extrema of exp(-x)R are same roots.
if [2 * c for c in p] != [6, -6, 1]:
    raise ValueError("root factorization")
if not F(5, 3) ** 2 < 3 < F(7, 4) ** 2:
    raise ValueError("radical brackets")
# Positive series lower bounds suffice for upper bounds on negative exponentials.
first_series = sum((F(5, 4) ** i / factorial(i) for i in range(6)), F(0))
second_series = sum((F(14, 3) ** i / factorial(i) for i in range(9)), F(0))
if first_series <= F(10, 3) or second_series <= 64:
    raise ValueError("exponential reciprocal bounds")
first = F(3, 4) * F(3, 10)
second = F(11, 4) * F(1, 64)
if max(first, second) >= 1:
    raise ValueError("disturbance extremum bound")
negative_area = (first + second) / 6
# Integral of exp(-x) P/6 is 1/6, plus feedthrough5/6 => signed total1.
signed_continuous = sum((c * factorial(i) for i, c in enumerate(p)), F(0)) / 6
if signed_continuous != F(1, 6):
    raise ValueError("signed impulse mass")
l1 = 1 + 2 * negative_area
bound = 10 * l1 + F(4, 5)
saved = json.loads((BASE / "domain_exact_direct_bound_results.json").read_text())
if bound != F(saved["direct_absolute_actual_jerk_upper"]):
    raise ValueError("saved value binding")
witness = json.loads((BASE / "critic_nominal_jerk_results.json").read_text())
lower = F(witness["actual_jerk_lower"])
if lower <= bound:
    raise ValueError("no strict separation")
result = dict(
    negative_area_upper=str(negative_area),
    direct_global_peak_upper=str(bound),
    candidate_at_1_over_20_lower=str(lower),
    strict_gap_lower=str(lower - bound),
    source_jerk_certificate="critic_bernstein_results.json:64 subintervals checked",
    initial_conditions="q,qprime,qdoubleprime and e,eprime,edoubleprime zero; j(0)=10; constantw=.01; direct algebraic initialu5/48",
    scope="Hand convolution and ODE argument supported by independently reproduced rational inequalities; not Lean or robot validation",
)
(BASE / "critic_direct_bound_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
