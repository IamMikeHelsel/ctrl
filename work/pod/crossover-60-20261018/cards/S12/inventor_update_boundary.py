"""Separate action summaries from update states; accuracy depends on readout center."""

import json
from fractions import Fraction as F
from pathlib import Path

from inventor_exact import actions, constraints, dot, enc, separated, vertices

# This corner exists in the action-sufficient (w,b) box, but not in the original
# feasible set. An observation of this exact pair therefore requires joint data.
w, b = F(27, 70), F(9, 10)
d = b - w
q_upper = F(3, 10) * d
assert d == F(18, 35) and q_upper == F(27, 175)
assert w + q_upper == F(27, 50) < F(3, 5)
assert min(p[0] for p in separated["1"]) == w
assert min(p[0] + p[1] for p in separated["1"]) == b
corner_obs = [((1, 0, 0), w), ((-1, 0, 0), -w), ((1, 1, 0), b), ((-1, -1, 0), -b)]
corner_joint = {str(sign): vertices(constraints(sign, True) + corner_obs) for sign in [1, -1]}
assert not any(corner_joint.values())
assert actions(corner_joint)["status"] == "MODEL_DATA_INCONSISTENT"


def exact_separating(center):
    return {
        str(sign): vertices(constraints(sign) + [((1, 0, 1), center), ((-1, 0, -1), -center)])
        for sign in [1, -1]
    }


def valid_baseline(p):
    return any(all(dot(row, p) <= rhs for row, rhs in constraints(sign)) for sign in [1, -1])


negative_worlds = [(F(-9, 10), F(2), F(3, 5)), (F(-3, 5), F(3, 2), F(3, 10))]
for p in negative_worlds:
    assert valid_baseline(p) and p[0] + p[2] == F(-3, 10)
    # Each already cannot satisfy the original mixed limit, even if identified.
    assert actions({"single": [p]})["safe_interval"] == []
assert negative_worlds[1][0] - negative_worlds[0][0] == F(3, 10) > F(1, 4)
negative = exact_separating(F(-3, 10))
assert any(negative.values()) and actions(negative)["safe_interval"] == []

# Stronger information-only trap: each witness permits an action, but the
# required common action cannot depend on the unobserved source attribution.
positive_worlds = [(F(1, 8), F(7, 8), F(7, 40)), (F(3, 80), F(7, 8), F(21, 80))]
for p in positive_worlds:
    assert valid_baseline(p) and p[0] + p[2] == F(3, 10)
individual = [actions({"single": [p]})["safe_interval"] for p in positive_worlds]
assert individual == [[F(-1, 4), F(-1, 4)], [F(-13, 80), F(-13, 80)]]
assert actions({"pair": positive_worlds})["safe_interval"] == []
positive = exact_separating(F(3, 10))
assert any(positive.values()) and actions(positive)["safe_interval"] == []
# An exact reading of the EXISTING baseline row distinguishes this pair.
# It does not establish that all other retained worlds have a safe action.
baseline_predictions = [p[0] + p[1] for p in positive_worlds]
assert baseline_predictions == [F(1), F(73, 80)]
separation = abs(baseline_predictions[0] - baseline_predictions[1])
assert separation == F(7, 80)
heldout_predictions = [p[0] + p[2] / 2 for p in positive_worlds]
assert heldout_predictions == [F(17, 80), F(27, 160)]
heldout_center = F(61, 320)
heldout_radius = F(7, 320)
assert all(abs(v - heldout_center) == heldout_radius for v in heldout_predictions)
assert heldout_radius < F(1, 40)
with_heldout = {
    str(sign): vertices(
        constraints(sign)
        + [((1, 0, 1), F(3, 10)), ((-1, 0, -1), F(-3, 10))]
        + [
            ((1, 0, F(1, 2)), heldout_center + F(1, 40)),
            ((-1, 0, F(-1, 2)), -heldout_center + F(1, 40)),
        ]
    )
    for sign in [1, -1]
}
assert any(with_heldout.values()) and actions(with_heldout)["safe_interval"] == []

# Failure persists with non-singleton individual safe-action intervals.
interior_worlds = [(F(6, 25), F(4, 5), F(4, 25)), (F(4, 25), F(4, 5), F(6, 25))]
for p in interior_worlds:
    assert valid_baseline(p) and p[0] + p[2] == F(2, 5)
interior_actions = [actions({"single": [p]})["safe_interval"] for p in interior_worlds]
assert interior_actions == [
    [F(-73, 200), F(-29, 100)],
    [F(-57, 200), F(-21, 100)],
]
gap = interior_actions[1][0] - interior_actions[0][1]
assert gap == F(1, 200) == F(11, 10) * F(4, 5) - F(7, 8)
assert actions({"pair": interior_worlds})["safe_interval"] == []

result = {
    "phantom_action_box_corner": {
        "w": w,
        "b": b,
        "implied_d": d,
        "maximum_q": q_upper,
        "maximum_separating_value": w + q_upper,
        "required_separating_minimum": F(3, 5),
        "marginally_admitted_but_jointly_inconsistent": True,
    },
    "perfect_separating_readout_negative_three_tenths": {
        "changed_center_diagnostic": True,
        "worlds": negative_worlds,
        "wheel_gap": F(3, 10),
        "each_world_individually_unsafe": True,
        "nonempty_and_no_common_action": True,
    },
    "perfect_separating_readout_positive_three_tenths": {
        "changed_center_diagnostic": True,
        "worlds": positive_worlds,
        "individual_action_intervals": individual,
        "pair_common_action_interval": [],
        "existing_baseline_row_predictions": baseline_predictions,
        "next_test": "Prospective baseline-row error strictly below 7/160 separates these two predicted observation intervals. Fresh shared-latent modeling required; reducing bounds through duplicate copies is invalid.",
        "claimed_scope": "Pair discrimination only; neither full feasible-set identification nor guaranteed action for every readout.",
        "half_leakage_heldout_predictions": heldout_predictions,
        "hypothetical_common_heldout_center": heldout_center,
        "both_retained_at_original_heldout_error_bound": F(1, 40),
        "pair_discrimination_error_must_be_strictly_less_than": heldout_radius,
        "heldout_scope": "Both separating and heldout centers changed for this diagnostic. Original sensor rows and error guarantees retained. At error7/320 midpoint61/320 still retains both; smaller error separates their prediction intervals, but does not prove full-set safety.",
    },
    "precision_threshold_scope": "Previously derived epsilon<=43/1000 is conditional on readout center exactly 5/8, baseline center1 error1/10, all original priors and safety limits. It is not a guarantee over every possible separating readout.",
    "interior_common_action_failure": {
        "changed_perfect_separating_center": F(2, 5),
        "worlds": interior_worlds,
        "individual_action_intervals": interior_actions,
        "strict_separation_between_action_intervals": gap,
        "family": "With fixed d in (35/44,7/8], lambda endpoints1/5,3/10, common separating center a and baseline-compatible worlds, action-interval gap=(11/10)d-7/8>0. This is not confined to singleton individual action sets.",
        "next_measurement": "The existing baseline row predicts26/25 versus24/25. A justified prospective error strictly below1/25 separates this pair; duplicated existing observations do not supply that guarantee.",
    },
    "evidence": "Exact rational finite model diagnostics, not Lean or physical sensing evidence.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(enc(result), indent=2) + "\n")
print(json.dumps(enc(result), indent=2))
