"""Exact sufficient rest-state admission for a septic reference; deliberately scoped."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def gate(request):
    # A receiver binds ALL retained state and time fields; no silent rest reset.
    allowed = {
        "initial",
        "terminal_derivatives",
        "latency_policy",
        "latency",
        "deadline",
        "distance",
        "velocity_limit",
        "acceleration_limit",
        "jerk_limit",
        "snap_limit",
        "corridor",
        "regularity",
    }
    if set(request) != allowed:
        return {"decision": "UNKNOWN", "reason": "unsupportedormissingfields"}
    if request["regularity"] != "AC_jerk_bounded_snap_ae":
        return {"decision": "UNKNOWN", "reason": "unsupportedregularity"}
    if request["initial"] != ["0"] * 4 or request["terminal_derivatives"] != ["0"] * 3:
        return {"decision": "UNKNOWN", "reason": "nonreststate unsupported"}
    if request["latency_policy"] != "hold_rest":
        return {"decision": "UNKNOWN", "reason": "latencymodel unsupported"}
    ell = F(request["latency"])
    if ell < 0:
        return {"decision": "UNKNOWN", "reason": "negativecausallatency"}
    T = F(request["deadline"]) - ell
    D = F(request["distance"])
    if T <= 0 or D < 0:
        return {"decision": "UNKNOWN", "reason": "outsidepositiveforwardhorizoncontract"}
    corridor = request.get("corridor")
    if corridor is None:
        return {"decision": "UNKNOWN", "reason": "missingcorridorcontract"}
    if F(corridor[0]) > 0 or F(corridor[1]) < D:
        return {"decision": "REJECT", "reason": "initialorgoaloutsidecorridor"}
    limits = {
        "velocity": F(35, 16) * D / T,
        "acceleration": F(105, 4) * D / T**2,
        "jerk": F(105, 2) * D / T**3,
        "snap": 840 * D / T**4,
    }
    if D > F(request["snap_limit"]) * T**4 / 384:
        return {"decision": "REJECT", "reason": "necessaryrestmomentdualgate"}
    if any(limits[k] > F(request[k + "_limit"]) for k in limits):
        return {"decision": "UNKNOWN", "reason": "septiccertificateinsufficient"}
    return {
        "decision": "ADMIT_REFERENCE",
        "bounds": {k: str(v) for k, v in limits.items()},
        "duration": str(T),
        "distance": str(D),
        "shape": "35s4-84s5+70s6-20s7",
        "scope": "Prospective reference only; polynomial derivative/corridor bridge separatelyproved, no plant guarantee",
    }


base = {
    "regularity": "AC_jerk_bounded_snap_ae",
    "corridor": ["0", "1/24000"],
    "initial": ["0"] * 4,
    "terminal_derivatives": ["0"] * 3,
    "latency_policy": "hold_rest",
    "latency": "1/200",
    "deadline": "21/200",
    "distance": "1/24000",
    "velocity_limit": "1",
    "acceleration_limit": "3",
    "jerk_limit": "10",
    "snap_limit": "400",
}
rows = [{"case": "positive", "request": base, "result": gate(base)}]
assert rows[0]["result"]["decision"] == "ADMIT_REFERENCE"
for name, change, expected in [
    ("impossiblejoint", {"distance": "1/1000"}, "REJECT"),
    ("unsupportednonrest", {"initial": ["0", "0", "1", "10"]}, "UNKNOWN"),
    ("wronghold", {"latency_policy": "continue_old"}, "UNKNOWN"),
    ("lessslack", {"deadline": "1/20"}, "REJECT"),
    ("septicgap", {"distance": "1/20000"}, "UNKNOWN"),
    ("wrongunits", {"distance": "1"}, "REJECT"),
    ("nonzeroendjerk", {"terminal_derivatives": ["0", "0", "1"]}, "UNKNOWN"),
    ("reverse_request", {"distance": "-1/24000"}, "UNKNOWN"),
    ("zero_horizon_hold", {"distance": "0", "deadline": "1/200"}, "UNKNOWN"),
    ("negativelatency", {"latency": "-1/200"}, "UNKNOWN"),
    ("shortcorridor", {"corridor": ["0", "1/30000"]}, "REJECT"),
    ("missingcorridor", {"corridor": None}, "UNKNOWN"),
    ("lateexecution", {"latency": "3/200"}, "UNKNOWN"),
    ("broadcorridor", {"corridor": ["-1", "1"]}, "ADMIT_REFERENCE"),
    ("continuoussnap", {"regularity": "continuous_snap"}, "UNKNOWN"),
    ("unexpectedconstraint", {"continuous_snap_required": True}, "UNKNOWN"),
]:
    r = {**base, "corridor": ["-1", "1"], **change}
    out = gate(r)
    assert out["decision"] == expected
    rows.append({"case": name, "request": r, "result": out})
(HERE / "pm_septic.json").write_text(
    json.dumps(
        {
            "cases": rows,
            "scope": "Exact arithmetic prototype; complete polynomial all-time certificate and kinematic binding are needed. UNKNOWN is notinfeasible.",
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(rows[0]["result"]))
