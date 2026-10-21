"""Exact static attribution tests; original model unchanged, diagnostics labeled."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution/model.json"
)
MODEL = json.loads(SOURCE.read_text())


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def solve(rows, rhs):
    a = [list(map(F, row)) + [F(b)] for row, b in zip(rows, rhs, strict=True)]
    for c in range(3):
        pivot = next((r for r in range(c, 3) if a[r][c]), None)
        if pivot is None:
            return None
        a[c], a[pivot] = a[pivot], a[c]
        v = a[c][c]
        a[c] = [x / v for x in a[c]]
        for r in range(3):
            if r != c:
                v = a[r][c]
                a[r] = [x - v * y for x, y in zip(a[r], a[c], strict=True)]
    return tuple(row[-1] for row in a)


def observation(key, error=None):
    s = MODEL[key]
    row = tuple(map(F, s["row"]))
    value = F(s["value"]) - F(s.get("wheel_offset", "0"))
    eps = F(s["error_bound"]) if error is None else error
    return [(row, value + eps), (tuple(-x for x in row), -value + eps)]


def constraints(sign, separated=False, duplicates=0, baseline_error=None):
    out = [
        ((F(1), F(0), F(0)), F(2)),
        ((F(-1), F(0), F(0)), F(2)),
        ((F(0), F(1), F(0)), F(2)),
        ((F(0), F(-1), F(0)), F(2)),
    ]
    low, high = map(F, MODEL["prior"]["lambda"])
    if sign == 1:
        out += [((0, -1, 0), 0), ((0, low, -1), 0), ((0, -high, 1), 0)]
    else:
        out += [((0, 1, 0), 0), ((0, high, -1), 0), ((0, -low, 1), 0)]
    out += observation("baseline", baseline_error) * (1 + duplicates)
    if separated:
        out += observation("separating")
    return [(tuple(map(F, a)), F(b)) for a, b in out]


def vertices(cs):
    # Deduplication affects only enumeration cost, never the feasible set.
    cs = list(dict.fromkeys(cs))
    out = set()
    for ids in combinations(range(len(cs)), 3):
        point = solve([cs[i][0] for i in ids], [cs[i][1] for i in ids])
        if point is not None and all(dot(a, point) <= b for a, b in cs):
            out.add(point)
    return sorted(out)


def worlds(separated=False, duplicates=0, baseline_error=None):
    return {
        str(sign): vertices(constraints(sign, separated, duplicates, baseline_error))
        for sign in [1, -1]
    }


def actions(vs):
    points = [p for branch in vs.values() for p in branch]
    if not points:
        return {"status": "MODEL_DATA_INCONSISTENT", "safe_interval": None}
    wlo, whi = min(p[0] for p in points), max(p[0] for p in points)
    slo, shi = min(p[0] + p[1] for p in points), max(p[0] + p[1] for p in points)
    wheel_limit = F(MODEL["acceptance"]["wheel_component_limit"])
    mixed_limit = F(MODEL["acceptance"]["mixed_response_limit"])
    lo = max(-wheel_limit - wlo, -mixed_limit - min(wlo, slo))
    hi = min(wheel_limit - whi, mixed_limit - max(whi, shi))
    return {
        "status": "NONEMPTY",
        "safe_interval": [lo, hi] if lo <= hi else [],
        "wheel_range": [wlo, whi],
        "baseline_range": [slo, shi],
    }


def accept(vs, c):
    envelope = actions(vs)
    interval = envelope["safe_interval"]
    return interval is not None and len(interval) == 2 and interval[0] <= c <= interval[1]


def enc(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {k: enc(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [enc(v) for v in x]
    return x


baseline = worlds()
duplicate = worlds(duplicates=100)
separated = worlds(True)
assert baseline == duplicate
assert constraints(1)[-2:] == observation("trial")
assert accept(separated, F(-1, 2)) and not accept(separated, F(-1))
envelope = actions(separated)
assert envelope["safe_interval"] == [F(-143, 280), F(-37, 80)]
# Original-model worlds whose convex midpoint violates the original joint relation.
a = (F(1, 2), F(1, 2), F(1, 10))
b = (F(3, 2), F(-1, 2), F(-3, 20))
assert all(dot(row, a) <= rhs for row, rhs in constraints(1))
assert all(dot(row, b) <= rhs for row, rhs in constraints(-1))
mid = tuple((x + y) / 2 for x, y in zip(a, b, strict=True))
assert mid == (F(1), F(0), F(-1, 40))
assert not any(all(dot(row, mid) <= rhs for row, rhs in constraints(sign)) for sign in [1, -1])
# Diagnostic extra joint observation (not one of the original sensor rows).
extra = [((0, 1, 0), 0), ((0, -1, 0), 0), ((0, 0, 1), F(-1, 40)), ((0, 0, -1), F(1, 40))]
extra = [(tuple(map(F, row)), F(rhs)) for row, rhs in extra]
empty = {str(sign): vertices(constraints(sign) + extra) for sign in [1, -1]}
assert not any(empty.values()) and not accept(empty, F(-1, 2))
# Deliberately wrong information fusion: four copies do not halve a deterministic bound.
wrong = worlds(True, baseline_error=F(1, 20))
probe = F(-23, 50)
assert accept(wrong, probe) and not accept(separated, probe)
witness = (F(47, 80), F(5, 16), F(1, 16))
assert all(dot(row, witness) <= rhs for row, rhs in constraints(1, True))
assert witness[0] + probe == F(51, 400) > F(1, 8)
# Original scalar heldout is compatibility-only, with one convex surviving branch.
pts = separated["1"]
held = [p[0] + p[2] / 2 for p in pts]
observed = [F(43, 80), F(47, 80)]
assert min(held) < observed[0] and max(held) > observed[1]
result = {
    "model_source": str(SOURCE),
    "baseline_action_envelope": actions(baseline),
    "separated_action_envelope": envelope,
    "same_baseline_after_100_exact_duplicates": True,
    "trial_constraints_equal_baseline_after_known_offset": True,
    "preserved_original_actions": {str(c): accept(separated, F(c)) for c in MODEL["actions"]},
    "joint_hull_diagnostic": {
        "original_feasible_worlds": [a, b],
        "nonphysical_convex_midpoint": mid,
        "added_observation": "d=0, q=-1/40; hypothetical diagnostic, not available original scalar heldout",
        "concrete_branches_empty": True,
        "hull_contains_observation_witness": True,
        "guard_status": actions(empty)["status"],
    },
    "false_confidence_diagnostic": {
        "invalid_change": "halve baseline deterministic error bound after four duplicate copies",
        "probe_action": probe,
        "probe_not_in_original_declared_action_list": True,
        "wrong_accept": True,
        "correct_reject": True,
        "retained_counterexample": witness,
        "wheel_residual": F(51, 400),
        "limit": F(1, 8),
    },
    "heldout_original": {
        "prediction_interval": [min(held), max(held)],
        "observation_interval": observed,
        "compatible": True,
        "all_retained_worlds_predict_observation": False,
        "surviving_branches": [key for key, v in separated.items() if v],
    },
    "scope": "Exact rational finite polytope computation; vertex method trusted; not Lean, statistics, dynamic stopping or hardware evidence.",
}
Path(__file__).with_name("inventor_exact.json").write_text(json.dumps(enc(result), indent=2) + "\n")
print(json.dumps(enc(result), indent=2))
