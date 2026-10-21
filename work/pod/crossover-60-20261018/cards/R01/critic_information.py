"""Exact finite information obstructions and declared protocol failure witnesses."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent


def intersect(sets):
    result = set.union(*map(set, sets))
    for item in sets:
        result &= set(item)
    return result


def feasible_encoding(tasks, labels):
    for label in set(labels):
        group = [task for task, assigned in zip(tasks, labels, strict=True) if assigned == label]
        if not intersect(group):
            return False
    return True


def minimum_labels(tasks):
    for count in range(1, len(tasks) + 1):
        for labels in itertools.product(range(count), repeat=len(tasks)):
            if feasible_encoding(tasks, labels):
                return count, labels
    raise AssertionError("Each task must be individually feasible")


# Millimetres. Identical numeric observations do not choose between task meanings.
hold = (F(-1, 5), F(1, 5))
move = (F(4, 5), F(6, 5))
assert max(hold[0], move[0]) > min(hold[1], move[1])
# Any randomized shared output distribution has disjoint success events, hence
# p_hold+p_move <= 1: worst-case success <= 1/2. No distribution assumptions needed.

# Permission means choose any acceptable point; uncertainty means satisfy every truth.
goal_uncertainty = [F(-1), F(1)]
epsilon = F(1, 5)
robust = (max(g - epsilon for g in goal_uncertainty), min(g + epsilon for g in goal_uncertainty))
assert robust[0] > robust[1]
assert F(0) >= min(goal_uncertainty) and F(0) <= max(goal_uncertainty)

# Declared extension to finite trajectory choices: pairwise conflict graphs miss
# a three-way obstruction. Each letter represents a complete admissible trajectory.
tasks = [set("ab"), set("bc"), set("ac")]
assert all(tasks[i] & tasks[j] for i in range(3) for j in range(i + 1, 3))
assert not intersect(tasks)
count, labels = minimum_labels(tasks)
assert count == 2
assert minimum_labels([set("a"), set("b")])[0] == 2
assert minimum_labels([set("ab"), set("bc")])[0] == 1

# Latency witness. If the sideband distinguishing move from hold is delivered after
# the fixed deadline, the histories available at the deadline remain identical.
deadline, delivery = F(1), F(11, 10)
hold_history = [(F(0), "OBSERVE", F(1))]
move_history = hold_history + [(delivery, "REVISE", F(1))]
assert [m for m in hold_history if m[0] <= deadline] == [
    m for m in move_history if m[0] <= deadline
]

# A deadband at1 mm permanently suppresses a genuine0.5 mm target.
assert all(abs(F(1, 2)) <= F(1) for _ in range(10))
# Strict progress from the existing tube is absent for small displacement<=R.
radius, delta = F(1, 5), F(1, 10)
assert delta - radius <= 0
# Goal completion within0.2mm does not necessarily imply any positive movement.
assert abs(F(0) - delta) <= radius

result = {
    "original_hold_move_bands_mm": [hold, move],
    "packet_only_universal_guarantee": False,
    "randomized_worst_case_success_upper_bound": "1/2, for these two disjoint task sets",
    "uncertain_goal_robust_interval_mm": robust,
    "trajectory_hypergraph_extension": {
        "tasks": [sorted(t) for t in tasks],
        "pairwise_incompatible_edges": 0,
        "minimum_labels": count,
        "example_encoding": labels,
    },
    "delivery_after_deadline_indistinguishable": True,
    "small_move_completion_can_allow_zero_motion": True,
    "scope": "Exact finite examples and information argument. No learned intent inference, physical controller validation, or general minimum bit count.",
}
(P / "critic_information_results.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(json.dumps(result, default=str))
