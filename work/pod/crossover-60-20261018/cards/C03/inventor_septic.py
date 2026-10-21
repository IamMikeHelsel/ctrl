"""Independent exact polynomial audit and isolated gate probes; no producer writes."""

import ast
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
raw = (HERE / "pm_septic.py").read_bytes()
root = ast.parse(raw.decode())
gate_node = next(
    node for node in root.body if isinstance(node, ast.FunctionDef) and node.name == "gate"
)
env = {"F": F}
exec(compile(ast.Module(body=[gate_node], type_ignores=[]), "<isolated-septic-gate>", "exec"), env)
gate = env["gate"]
base = json.loads((HERE / "pm_septic.json").read_text())["cases"][0]["request"]
coefficients = [F(0)] * 4 + [F(35), -F(84), F(70), -F(20)]
derivatives = [coefficients]
for _ in range(4):
    derivatives.append([i * c for i, c in enumerate(derivatives[-1])][1:])


def value(p, x):
    return sum((c * x**i for i, c in enumerate(p)), F(0))


D, T = F(1, 24000), F(1, 10)
assert [value(p, F(0)) for p in derivatives[:4]] == [0] * 4
assert [value(p, F(1)) for p in derivatives[:4]] == [1, 0, 0, 0]
assert derivatives[4] == list(map(F, [840, -10080, 25200, -16800]))
for k in range(1001):
    s = F(k, 1000)
    z, r = s * (1 - s), 1 - 2 * s
    assert value(derivatives[1], s) == 140 * z**3
    assert value(derivatives[4], s) / 840 == (5 * r**3 - 3 * r) / 2
    # Factor proofs below establish both sides of the continuous snap bound.
    assert 1 - (5 * r**3 - 3 * r) / 2 == (1 - r) * (5 * (r + F(1, 2)) ** 2 + F(3, 4)) / 2
    assert 1 + (5 * r**3 - 3 * r) / 2 == (1 + r) * (5 * (r - F(1, 2)) ** 2 + F(3, 4)) / 2
    assert 0 <= value(derivatives[0], s) <= 1
    assert abs(D / T**4 * value(derivatives[4], s)) <= 350
cases = {}
for name, change in {
    "positive": {},
    "incoming_jerk": {"initial": ["0", "0", "0", "1"]},
    "negative_latency": {"latency": "-1/200"},
    "narrow_external_corridor": {"corridor_lower": "0", "corridor_upper": "1/48000"},
    "continuous_snap_requested": {"continuous_snap_required": True},
}.items():
    request = {**base, **change}
    cases[name] = {"request": request, "result": gate(request)}
assert cases["positive"]["result"]["decision"] == "ADMIT_REFERENCE"
assert cases["incoming_jerk"]["result"]["decision"] == "UNKNOWN"
# External corridor/continuity fields are outside this prototype's schema.
assert D > F(cases["narrow_external_corridor"]["request"]["corridor_upper"])
out = {
    "producer_sha256": hashlib.sha256(raw).hexdigest(),
    "exact_derivative_coefficients": [list(map(str, p)) for p in derivatives],
    "joins": {
        "q_v_a_j_continuous": True,
        "snap_just_inside_start": "350",
        "snap_just_inside_end": "-350",
        "snap_in_rest": "0",
        "C4_or_bounded_crackle_claim": False,
    },
    "corridor": "Reference lies in[0,D] continuously by monotonicity; positive physical tracking error at final endpoint can leave it.",
    "probes": cases,
    "scope": "Continuum facts use displayed factorizations and derivative monotonicity, not1001samples as proof. No producer file modified.",
}
(HERE / "inventor_septic.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "producer_sha256": out["producer_sha256"],
            "decisions": {k: v["result"]["decision"] for k, v in cases.items()},
            "joins": out["joins"],
        },
        indent=2,
    )
)
