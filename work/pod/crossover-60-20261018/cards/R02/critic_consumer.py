"""Independent source-bound consumer of the domain boundary ledger and pulse diagnostic."""

import copy
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from critic_clocks import S, command, jet, schedules

P = Path(__file__).parent
D = json.loads((P / "domain_audit.json").read_text())
source = {(x["case"], x["method"]): x for x in schedules if x["method"].startswith("ruckig")}


def check(c):
    assert set(c["source_sha256"]) == {
        "native_execution.cpp",
        "profile_export.hpp",
        "make_references.py",
        "run_comparison.py",
        "reference-schedules.json",
    }
    for name, h in c["source_sha256"].items():
        assert hashlib.sha256((S / name).read_bytes()).hexdigest() == h
    rows = c["schedules"]
    assert len(rows) == len(source)
    assert len({(r["case"], r["method"]) for r in rows}) == len(source)
    for row in rows:
        pieces = source[(row["case"], row["method"])]["pieces"]
        assert len(row["jumps"]) == len(pieces) - 1
        total = F(0)
        for left, right, item in zip(pieces[:-1], pieces[1:], row["jumps"], strict=True):
            t = F(right["start_exact"])
            assert F(item["t"]) == t == F(left["end_exact"])
            assert item["left_origin"] == left["origin"] and item["right_origin"] == right["origin"]
            lj, rj = jet(left, t), jet(right, t)
            delta = [r - l for l, r in zip(lj[:4], rj[:4], strict=True)]
            assert delta == list(map(F, item["delta_qva_jerk"]))
            du = command(rj) - command(lj)
            assert du == F(item["delta_command_fixed_state"])
            total += abs(du)
        assert total == F(row["exact_command_jump_TV"])


check(D)
negative = []
for kind in [
    "omitted_boundary",
    "duplicate_boundary",
    "wrong_time",
    "wrong_side",
    "wrong_jump",
    "wrong_source_hash",
]:
    d = copy.deepcopy(D)
    j = d["schedules"][0]["jumps"]
    if kind == "omitted_boundary":
        j.pop(0)
    elif kind == "duplicate_boundary":
        j[1] = copy.deepcopy(j[0])
    elif kind == "wrong_time":
        j[0]["t"] = "0"
    elif kind == "wrong_side":
        j[0]["left_origin"], j[0]["right_origin"] = j[0]["right_origin"], j[0]["left_origin"]
    elif kind == "wrong_jump":
        j[0]["delta_command_fixed_state"] = "0"
    else:
        d["source_sha256"]["native_execution.cpp"] = "0" * 64
    try:
        check(d)
    except AssertionError:
        negative.append(kind)
    else:
        raise AssertionError(kind)
# Independently integrate producer pulse from coefficients using scalar polynomials.
H = json.loads((P / "inventor_hidden.json").read_text())
state = [F(0)] * 3
js = [F(0)]
for piece in H["pieces"]:
    assert state == list(map(F, piece["state"]))
    h = F(piece["hi"]) - F(piece["lo"])
    j = F(piece["jerk"])
    q, v, a = state
    state = [q + v * h + a * h * h / 2 + j * h**3 / 6, v + a * h + j * h * h / 2, a + j * h]
    js.append(j)
assert state == [0, 0, 0]
js.append(F(0))
tv = sum(abs(a - b) for a, b in zip(js[1:], js[:-1], strict=True))
assert tv == 40 and tv / 96 == F(5, 12)
for k in range(1001):
    assert not F(H["pieces"][0]["lo"]) < F(k, 1000) < F(H["pieces"][-1]["hi"])
(P / "critic_consumer.json").write_text(
    json.dumps(
        {
            "histories": 12,
            "boundaries": sum(len(r["jumps"]) for r in D["schedules"]),
            "mutations_rejected": negative,
            "hidden_pulse_endpoint": list(map(str, state)),
            "hidden_pulse_command_jump_tv": str(tv / 96),
            "scope": "Consumer binds frozen exported polynomial semantics and saved source hashes. No native-runtime or physical equivalence claim.",
        },
        indent=2,
    )
    + "\n"
)
print(
    "Domain all-boundary ledger and hidden-pulse diagnostic independently consumed; six semantic corruptions rejected"
)
