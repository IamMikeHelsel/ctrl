"""Exact finite/interval counterexamples to unsafe attribution-to-action shortcuts."""

import json
from fractions import Fraction as F
from pathlib import Path


def overlap(a, b):
    return max(a[0], b[0]) <= min(a[1], b[1])


def compatible(branches, observation):
    return any(overlap(branch, observation) for branch in branches)


def robust_safe(branches, action, limit):
    return bool(branches) and all(
        max(abs(lo + action), abs(hi + action)) <= limit for lo, hi in branches
    )


def safe_actions(branches, limit):
    if not branches:
        return None
    lower = max(-limit - lo for lo, _ in branches)
    upper = min(limit - hi for _, hi in branches)
    return [lower, upper] if lower <= upper else None


branches = [(F(-2), F(-1)), (F(1), F(2))]
heldout = (F(-1, 4), F(1, 4))
hull = (min(lo for lo, _ in branches), max(hi for _, hi in branches))
if compatible(branches, heldout) or not overlap(hull, heldout):
    raise ValueError("disconnected counterexample failed")
worlds = [(F(-1), F(-1)), (F(1), F(1))]
pointwise = [safe_actions([world], F(1, 2)) for world in worlds]
if not all(pointwise) or safe_actions(worlds, F(1, 2)) is not None:
    raise ValueError("action quantifier counterexample failed")
if robust_safe([], F(100), F(1, 2)) or not all([]):
    raise ValueError("nonempty guard counterexample failed")
# An outer hull may certify a universal bound conservatively, but not existential support.
# Every action certified on a hull must be certified on each retained branch.
checked = 0
for n in range(-12, 13):
    action = F(n, 4)
    for m in range(1, 17):
        limit = F(m, 4)
        if robust_safe([hull], action, limit) and not robust_safe(branches, action, limit):
            raise ValueError("outer universal implication failed")
        checked += 1
# One shared bounded error, copied four times, still allows theta=1,error=-1.
truth, error = F(1), F(-1)
observations = [truth + error] * 4
if observations != [0] * 4 or abs(truth) > 1 or abs(truth) <= F(1, 2):
    raise ValueError("duplicate evidence witness failed")
# Shared-error cancellation may help: y1=theta+b, y2=phi+b => theta-phi=y1-y2.
# Forgetting shared error gives a conservative difference interval[-2,2], not false precision.
result = dict(
    disconnected=dict(
        branches=branches, heldout=heldout, hull=hull, exact_compatible=False, hull_overlap=True
    ),
    quantifiers=dict(
        worlds=worlds, pointwise_safe_action_sets=pointwise, common_safe_action_set=None
    ),
    emptyset=dict(unguarded_universal=True, acceptance_with_guard=False),
    duplicate=dict(
        theta=truth,
        shared_error=error,
        copies=observations,
        true_theta_set=[-1, 1],
        false_four_independent_standard_error_set=[F(-1, 2), F(1, 2)],
        truth_wrongly_excluded=True,
    ),
    outer_universal_implications_checked=checked,
    scope="Exact synthetic rational counterexamples and finite implication checks, not physical safety or general Lean theorem",
)
Path(__file__).with_name("critic_cases_results.json").write_text(
    json.dumps(result, default=str, indent=2) + "\n"
)
print(json.dumps(result, default=str, indent=2))
