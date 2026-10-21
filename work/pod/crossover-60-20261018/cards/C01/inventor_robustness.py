"""Predeclared fixed-gain relocated-filter screen; no gain retuning."""

import json
from pathlib import Path

from inventor_relocated import run


def case(rate, disturbance, step):
    base = run(0, None, step, rate, disturbance)
    candidate = run(1 / 960, None, step, rate, disturbance)
    names = [
        "peak_error_m",
        "actual_jerk_squared_integral",
        "command_TV_including_initial_jump",
        "peak_actual_jerk",
    ]
    deltas = {name: candidate[name] - base[name] for name in names}
    return {
        "actuator_rate": rate,
        "disturbance": disturbance,
        "step": step,
        "direct": base,
        "relocated_fixed_g_1_over_960": candidate,
        "candidate_minus_direct": deltas,
        "sampled_tracking_both_pass": base["sampled_tracking_pass"]
        and candidate["sampled_tracking_pass"],
        "improves_jerk_integral_and_TV": deltas["actual_jerk_squared_integral"] < 0
        and deltas["command_TV_including_initial_jump"] < 0,
    }


results = [case(r, w, 0.0001) for r in [80, 100, 120] for w in [-0.01, 0, 0.01]]
# Recheck all nine rather than select a favorable refinement subset.
refined = [case(r, w, 0.00005) for r in [80, 100, 120] for w in [-0.01, 0, 0.01]]
out = {
    "fixed_parameters": {
        "g": "1/960",
        "filter_rate": 20,
        "feedback": [800, 60, 0.5],
        "direct_jerk_feedforward": "1/96",
        "initial_reference_and_physical_errors": 0,
        "initial_new_filter_state": 0,
        "task_and_reference": "unchanged causal-stop05 reference, horizon1.5s",
        "architecture": "Direct feedback retained; slow filter acts only on added jerk feedforward, not total actuator command",
    },
    "coarse": results,
    "refined": refined,
}
Path(__file__).with_name("inventor_robustness.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        [
            {
                k: r[k]
                for k in [
                    "actuator_rate",
                    "disturbance",
                    "candidate_minus_direct",
                    "sampled_tracking_both_pass",
                    "improves_jerk_integral_and_TV",
                ]
            }
            for r in refined
        ],
        indent=2,
    )
)
