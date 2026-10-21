"""Finite task-information and precision tests; units are millimeters."""

import json
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, list):
        return [encode(v) for v in x]
    if isinstance(x, tuple):
        return [encode(v) for v in x]
    if isinstance(x, dict):
        return {k: encode(v) for k, v in x.items()}
    return x


def common_interval(intervals):
    lo, hi = max(x[0] for x in intervals), min(x[1] for x in intervals)
    return [lo, hi] if lo <= hi else []


def admissible_encoding(goals, alphabet_size, epsilon):
    valid = []
    for assignment in product(range(alphabet_size), repeat=len(goals)):
        groups = [
            [
                (g - epsilon, g + epsilon)
                for g, code in zip(goals, assignment, strict=True)
                if code == label
            ]
            for label in set(assignment)
        ]
        if all(common_interval(group) for group in groups):
            valid.append(assignment)
    return valid


goals = [F(0), F(1, 2), F(1)]
epsilon = radius = F(1, 5)
observation = F(1)
assert all(abs(observation - g) <= 1 for g in goals)
assert not admissible_encoding(goals, 1, epsilon)
assert not admissible_encoding(goals, 2, epsilon)
assert len(admissible_encoding(goals, 3, epsilon)) == 6
revise_only = [0, 1, 1]
assert common_interval([(g - epsilon, g + epsilon) for g in goals[1:]]) == []
# This is a finite fixed-alphabet lower bound, not a universal minimum-bit claim.

# A tolerance-overlap control prevents overclaiming that every intent must be
# separately identified to meet the original position predicate.
overlapping_goals = [F(0), F(1, 10)]
assert common_interval([(g - epsilon, g + epsilon) for g in overlapping_goals]) == [
    F(-1, 10),
    F(1, 5),
]
assert admissible_encoding(overlapping_goals, 1, epsilon)
# But when only the full tracking tube is promised, robust reference margin0
# makes two distinct exact-goal uncertainties incompatible.
margin = epsilon - radius
assert margin == 0
true_goal_interval = [F(999, 1000), F(1001, 1000)]
robust_reference = common_interval([(g - margin, g + margin) for g in true_goal_interval])
assert robust_reference == []
q, true_goal, allowed_x = F(1), F(1001, 1000), F(4, 5)
assert abs(allowed_x - q) == radius
assert abs(allowed_x - true_goal) == F(201, 1000) > epsilon


# Optional channel-corruption extension, clearly distinct from noisy sensing.
# Three semantic targets need a codebook with pairwise distance>=3 to correct
# one flipped command bit. Exhaustively find the minimum length up through5.
def hamming(a, b):
    return (a ^ b).bit_count()


minimum_length = None
codebook = None
for n in range(1, 6):
    candidate = next(
        (
            words
            for words in combinations(range(2**n), 3)
            if all(hamming(a, b) >= 3 for a, b in combinations(words, 2))
        ),
        None,
    )
    if candidate is not None:
        minimum_length, codebook = n, candidate
        break
assert minimum_length == 5
for i, word in enumerate(codebook):
    for mask in [0] + [1 << j for j in range(minimum_length)]:
        received = word ^ mask
        compatible = [j for j, other in enumerate(codebook) if hamming(other, received) <= 1]
        assert compatible == [i]
# A perfectly transmitted but falsely assigned semantic label is undetectable
# from codeword integrity; the receiving controller sees a valid hold code.
assert codebook[0] in codebook

result = {
    "units": "millimeters",
    "original_tolerances": {"task_epsilon": epsilon, "tracking_radius": radius},
    "finite_semantic_example": {
        "goals": goals,
        "identical_observation": observation,
        "noise_bound": 1,
        "binary_encodings_that_satisfy_all_position_bands": 0,
        "three_symbol_valid_encodings": 6,
        "revise_only_aliases_two_moves": True,
        "scope": "At least3 semantic symbols, thus2 fixed noiseless bits, for this predeclared finite goal alphabet and common sensor history; no universal bit lower bound claimed.",
    },
    "negative_control": {
        "overlapping_goals": overlapping_goals,
        "single_position_can_satisfy_both": True,
        "limit": "Position tolerance alone does not certify that an arbitrarily small intended motion actually occurred.",
    },
    "target_precision": {
        "uncertain_true_goal_interval": true_goal_interval,
        "robust_reference_set": robust_reference,
        "encoded_reference": q,
        "allowed_tracking_realization": allowed_x,
        "true_goal": true_goal,
        "goal_error": abs(allowed_x - true_goal),
        "scope": "Counterexample to deriving the original goal tolerance from the tracking tube alone after quantization; not a simulated physical plant failure.",
    },
    "optional_command_bit_error_model": {
        "one_bit_error_minimum_length_for_three_labels": minimum_length,
        "codebook": [format(word, f"0{minimum_length}b") for word in codebook],
        "all_radius_one_decodes_checked": True,
        "semantic_truth_not_established_by_valid_codeword": True,
        "scope": "Additional bounded command-corruption model, not part of the original noisy-observation task.",
    },
    "evidence": "Exact finite enumeration and rational interval arithmetic; no kernel or physical validation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(json.dumps(encode(result), indent=2))
