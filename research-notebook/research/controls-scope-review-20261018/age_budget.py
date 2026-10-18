"""Exact arithmetic feasibility screen, NOT a Lean proof or trajectory test.

The derivative bound is conditional on staying inside the existing hold cube
and on total target mismatch <= 2R. Closing that bootstrap for a sampled
implementation is still a proof obligation. No old artifact is modified.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

R = F(2221, 40000)
W = 2 * R
ex, ev, ea = F(1, 1000), F(1, 100), F(1, 20)
measurement = 8 * ex + 6 * ev + ea / 2
records = []
for r, signs, sw in product((F(8), F(12)), product((-1, 1), repeat=3), (-1, 1)):
    z1, z2, z3 = (s * R for s in signs)
    w = sw * W
    v = 4 * (z2-z1)
    a = 16 * (z1-2*z2+z3)
    command = 8*z1-8*z2-8*z3
    jerk = r * (command+w-a)
    physical_derivative = -8*v-6*a-jerk/2
    transformed_derivative = (4*r-64)*z1+(160-12*r)*z2+(12*r-96)*z3-r*w/2
    assert physical_derivative == transformed_derivative
    records.append({"r": str(r), "signs": signs, "w_sign": sw,
                    "command_derivative": str(physical_derivative)})

# The expression is affine in each of r,z1,z2,z3,w separately. Its absolute
# value on the box is bounded by the maximum at the 32 vertices.
derivative_bound = max(abs(F(row["command_derivative"])) for row in records)
assert derivative_bound == 104 * R
rows = []
for drive_error, age in product((F(0), F(1,100)), (F(0), F(1,2000), F(1,1000), F(2,1000), F(5,1000))):
    proposed_bound = measurement + derivative_bound*age + drive_error
    rows.append({"drive_error_m_per_s2": str(drive_error), "age_s": str(age),
                 "mismatch_bound_m_per_s2": str(proposed_bound),
                 "mismatch_bound_decimal": float(proposed_bound),
                 "fits_existing_budget": proposed_bound <= W,
                 "slack_m_per_s2": str(W-proposed_bound)})
assert [row["fits_existing_budget"] for row in rows] == [True, True, True, True, False, True, True, True, False, False]
thresholds = [{"drive_error_m_per_s2": str(d),
               "algebraic_age_ceiling_s": str((W-measurement-d)/derivative_bound),
               "algebraic_age_ceiling_ms": float(1000*(W-measurement-d)/derivative_bound)}
              for d in (F(0), F(1,100))]
out = {"status": "exact arithmetic screen passed; sampled invariance NOT proved",
       "R_m": str(R), "total_budget_m_per_s2": str(W),
       "measurement_cost_m_per_s2": str(measurement),
       "conditional_command_slope_m_per_s3": str(derivative_bound),
       "physical_speed_bound_m_per_s": str(8*R),
       "physical_acceleration_bound_m_per_s2": str(64*R),
       "measured_command_bound_m_per_s2": str(24*R+measurement),
       "vertices_checked": len(records), "vertices": records,
       "rows": rows, "thresholds": thresholds,
       "limits": ["No continuous-time proof, sampled execution, or existence result.",
                  "The cube and total mismatch assumptions need a noncircular invariant argument.",
                  "A failed sufficient budget does not imply unsafe motion.",
                  "Total information age includes sample age and command latency.",
                  "The one-off capture delay bound is a different contract.",
                  "Exact fractions checked by Python; not kernel-checked."]}
Path(__file__).with_name("age-budget-results.json").write_text(json.dumps(out, indent=2)+"\n")
print(json.dumps({k:out[k] for k in ("status", "measurement_cost_m_per_s2", "conditional_command_slope_m_per_s3", "thresholds")}))
