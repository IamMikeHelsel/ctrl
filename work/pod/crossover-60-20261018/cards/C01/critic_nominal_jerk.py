"""Independent rational exponential inequality for one nominal jerk witness."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

# exp(5/4): exact positive series through term8, geometric bound from term9.
x = F(5, 4)
partial = sum((x**n / F(factorial(n)) for n in range(9)), F(0))
first = x**9 / F(factorial(9))
upper = partial + first / (1 - x / 10)
if not upper < F(7, 2):
    raise ValueError("exponential upper bound failed")
t = F(1, 20)
coefficient = 25625 * t**3 - 9025 * t**2 + 706 * t - F(46, 5)
if coefficient != F(2157, 320):
    raise ValueError("coefficient binding failed")
jerk_lower = 10 + coefficient / upper
if not jerk_lower > F(119, 10):
    raise ValueError("jerk witness failed")
result = dict(
    time=str(t),
    coefficient=str(coefficient),
    exp_positive_upper=str(upper),
    actual_jerk_lower=str(jerk_lower),
    decimal=float(jerk_lower),
    scope="Nominal co-design actual jerk at one source old-plan time. Does not certify direct continuous peak, uncertainty, or kernel proof.",
)
Path(__file__).with_name("critic_nominal_jerk_results.json").write_text(
    json.dumps(result, indent=2) + "\n"
)
print(json.dumps(result, indent=2))
