"""Exact algebra for a four-box reference contract. No plant simulation.

Run from any directory with Python 3. All calculations use Fraction.
The script checks finite polynomial identities and extrema candidates. It is
not a Lean proof or an independent general-purpose polynomial prover.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import comb, factorial
import hashlib
import json

HERE = Path(__file__).resolve().parent

def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)

def deriv(p):
    return trim([i * p[i] for i in range(1, len(p))] or [Q(0)])

def val(p, x):
    return sum(c * x**i for i, c in enumerate(p))

def step_piece(k):
    """F(x)=sum_i (-1)^i C(4,i) (x-i)_+^4 / 24, k<=x<=k+1."""
    p = [Q(0)] * 5
    for i in range(k + 1):
        for j in range(5):
            p[j] += Q((-1)**i * comb(4, i) * comb(4, j) * (-i)**(4-j), 24)
    return trim(p)

pieces = [(Q(0),)] + [step_piece(k) for k in range(4)] + [(Q(1),)]
derivatives = []
for p in pieces:
    row = [p]
    for _ in range(4):
        row.append(deriv(row[-1]))
    derivatives.append(row)

# Exact equality of derivatives zero through three at every knot.
continuity = []
for x in range(5):
    for order in range(4):
        left = val(derivatives[x][order], Q(x))
        right = val(derivatives[x+1][order], Q(x))
        assert left == right
        continuity.append({"knot": x, "derivative": order, "value": str(left)})

# These rational candidate lists include every stationary point in its piece.
# The accompanying derivative-root checks record why the list is complete:
# F'' has roots 0, 2/3, 2, 10/3, 4; only 0,2,4 lie in their applicable pieces.
# F''' is linear in each piece and has applicable roots 0,4/3,8/3,4.
velocity_roots = [[Q(0)], [Q(2,3), Q(2)], [Q(2), Q(10,3)], [Q(4)]]
accel_roots = [[Q(0)], [Q(4,3)], [Q(8,3)], [Q(4)]]
for k in range(4):
    for root in velocity_roots[k]:
        assert val(derivatives[k+1][2], root) == 0
    for root in accel_roots[k]:
        assert val(derivatives[k+1][3], root) == 0

extrema = {}
for order, roots in [(1, velocity_roots), (2, accel_roots), (3, [[]]*4), (4, [[]]*4)]:
    candidates = []
    for k in range(4):
        xs = [Q(k), Q(k+1)] + [x for x in roots[k] if k <= x <= k+1]
        for x in xs:
            candidates.append({"piece": k, "x": str(x), "value": str(val(derivatives[k+1][order], x))})
    extremum = max(abs(Q(c["value"])) for c in candidates)
    extrema[str(order)] = {"max_abs": str(extremum), "candidates": candidates}
assert [extrema[str(i)]["max_abs"] for i in range(1,5)] == ["2/3", "2/3", "2", "3"]

# A tail polynomial formed from all five truncated-power terms equals one.
assert step_piece(4) == (Q(1),)
assert val(pieces[3], Q(2)) == Q(1,2)

h, variation, sigma, W, R = Q(1,5), Q(3,100), Q(10), Q(1,100), Q(1,5000)
V = Q(2,3) * variation / h
A = Q(2,3) * variation / h**2
J = 2 * variation / h**3
S = 3 * variation / h**4
budget_left = W + J / (48*sigma)
budget_right = 2*sigma**2*R
assert budget_left <= budget_right

# Express the physical lag residual through the inherited tracking cube.
# z=(ex, ex+ev/(4*sigma), ex+ev/(2*sigma)+ea/(16*sigma^2)).
# u+w-a = sigma^2*(-8*z0+24*z1-24*z2)+(5/(48*sigma))*j+w.
# Equality is checked coefficient-wise on the three coordinate basis vectors.
for z0,z1,z2 in [(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1))]:
    ex = z0
    ev = 4*sigma*(z1-z0)
    ea = 16*sigma**2*(z2-2*z1+z0)
    assert -8*sigma**2*ex-6*sigma*ev-Q(3,2)*ea == sigma**2*(-8*z0+24*z1-24*z2)

single_delta = Q(1,50)
negative_delta = Q(1,20)
result = {
    "status": "exact finite algebra passed; general theorem and plant simulation remain open",
    "kernel": "four cascaded equal-width box filters; F is the causal step response",
    "parameter_units": {"h": "s", "variation": "m", "sigma": "1/s", "W": "m/s^2", "R": "m"},
    "parameters": {"h": str(h), "variation": str(variation), "sigma": str(sigma), "W": str(W), "R": str(R)},
    "reference_bounds": {"velocity_m_s": str(V), "acceleration_m_s2": str(A), "jerk_m_s3": str(J), "snap_m_s4_away_from_knots": str(S), "finite_tail_s": str(4*h)},
    "tracking_budget": {"left_m_s2": str(budget_left), "right_m_s2": str(budget_right), "minimum_sufficient_R_m": str(budget_left/(2*sigma**2))},
    "conservative_physical_bounds": {"velocity_m_s": str(V+8*sigma*R), "acceleration_m_s2": str(A+64*sigma**2*R), "command_m_s2": str(A+24*sigma**2*R+5*J/(48*sigma)), "actual_jerk_m_s3": str(12*sigma*(56*sigma**2*R+5*J/(48*sigma)+W))},
    "negative_cases": {
        "half_support_deadline": {"delta_m": str(single_delta), "time_after_accept_s": str(2*h), "reference_m": str(single_delta/2), "goal_error_m": str(single_delta/2)},
        "variation_budget_failure": {"delta_m": str(negative_delta), "allowed_variation_m": str(variation), "peak_reference_jerk_m_s3": str(2*negative_delta/h**3), "certified_reference_jerk_limit_m_s3": str(J)},
        "half_jerk_constant_mutation": {"correct_unit_step_peak": "2", "false_proposed_peak": "1", "witness_normalized_time": "2"},
        "disturbance_jump": {"rate_1_s": "120", "jump_w_m_s2": "1/100", "actual_jerk_jump_m_s3": "6/5", "assumption": "u and a retained; reference remains C3"}
    },
    "continuity_checks": continuity,
    "kernel_extrema": extrema,
    "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
coefficients = {"coefficient_order": "ascending powers of normalized time", "pieces": [{"interval": "x<0" if i==0 else "x>4" if i==5 else f"{i-1}<=x<={i}", "derivatives": [[str(c) for c in p] for p in row]} for i,row in enumerate(derivatives)]}
(HERE / "kernel-coefficients.json").write_text(json.dumps(coefficients, indent=2)+"\n")
(HERE / "exact-results.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({"passed": True, "reference_bounds": result["reference_bounds"], "tracking_budget": result["tracking_budget"], "conservative_physical_bounds": result["conservative_physical_bounds"]}, indent=2))
