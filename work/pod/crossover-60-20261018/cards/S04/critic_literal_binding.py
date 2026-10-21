"""Independent literal-statement audit; no producer/checker imports."""

import ast
import hashlib
import json
import re
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution"
)
MODEL = json.loads((SRC / "model.json").read_text())
RESULT = json.loads((SRC / "results.json").read_text())
OBJECTIVES = {
    "wheel": (1, 0, 0),
    "drivetrain": (0, 1, 0),
    "baseline_response": (1, 1, 0),
    "held_out_prediction": (1, 0, F(1, 2)),
}
RAT = re.compile(r"\((-?\d+) / (\d+) : ℝ\)")


def value(raw, env):
    clean = RAT.sub(lambda m: "(" + m[1] + "/" + m[2] + ")", raw).replace("(0 : ℝ)", "0")

    def walk(n):
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return F(n.value)
        if isinstance(n, ast.Name):
            return F(env[n.id])
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            return -walk(n.operand)
        if isinstance(n, ast.BinOp):
            a, b = walk(n.left), walk(n.right)
            if isinstance(n.op, ast.Add):
                return a + b
            if isinstance(n.op, ast.Sub):
                return a - b
            if isinstance(n.op, ast.Mult):
                return a * b
            if isinstance(n.op, ast.Div):
                return a / b
        raise AssertionError(ast.dump(n))

    return walk(ast.parse(clean, mode="eval").body)


def linear(raw):
    zero = dict.fromkeys("wdq", 0)
    c = value(raw, zero)
    a = tuple(value(raw, {**zero, k: 1}) - c for k in "wdq")
    return a, c


def model_rows(stage, sign):
    rows = set()
    for i, key in enumerate(("w", "d")):
        low, high = map(F, MODEL["prior"][key])
        for s, b in ((1, high), (-1, -low)):
            a = [F(0)] * 3
            a[i] = F(s)
            rows.add((tuple(a), b))
    lo, hi = map(F, MODEL["prior"]["lambda"])
    # Sign chooses the order of lambda*d endpoints.
    if sign == "nonnegative_d":
        rows |= {((0, -1, 0), F(0)), ((0, lo, -1), F(0)), ((0, -hi, 1), F(0))}
    else:
        rows |= {((0, 1, 0), F(0)), ((0, hi, -1), F(0)), ((0, -lo, 1), F(0))}
    names = ["baseline"]
    if stage in ("trial", "separated"):
        names.append("trial")
    if stage == "separated":
        names.append("separating")
    for name in names:
        reading = MODEL[name]
        center = F(reading["value"]) - F(reading.get("wheel_offset", "0"))
        for s in (1, -1):
            rows.add(
                (tuple(s * F(x) for x in reading["row"]), s * center + F(reading["error_bound"]))
            )
    return rows


def audit(text):
    blocks = dict(
        re.findall(r"^theorem (\w+)(.*?)(?=^theorem |^end CampaignS04Source)", text, re.S | re.M)
    )
    expected_names = set()
    counts = [0, 0, 0]
    assert set(RESULT["stages"]) == {"baseline", "duplicate", "trial", "separated"}
    for stage, item in RESULT["stages"].items():
        assert set(item["branches"]) == {"nonnegative_d", "nonpositive_d"}
        for sign, branch in item["branches"].items():
            rows = [(tuple(map(F, r["a"])), F(r["b"])) for r in branch["constraints"]]
            assert set(rows) == model_rows(stage, sign)
            prefix = stage + "_" + sign
            todo = (
                [(prefix + "_empty", None, None)]
                if not branch["feasible"]
                else [
                    (prefix + "_" + obj + "_" + side, obj, side)
                    for obj in OBJECTIVES
                    for side in ("lower", "upper")
                ]
            )
            for name, obj, side in todo:
                expected_names.add(name)
                block = blocks[name]
                hyps = re.findall(r"^    \(h(\d+) : (.*?) ≤ (\(-?\d+ / \d+ : ℝ\))\)", block, re.M)
                assert len(hyps) == len(rows)
                for index, (num, lhs, rhs) in enumerate(hyps):
                    assert int(num) == index
                    a, c = linear(lhs)
                    assert (a, value(rhs, {}) - c) == rows[index]
                conclusion = block.split(" := by", 1)[0].rsplit(") : ", 1)[1]
                if obj is None:
                    assert conclusion == "False"
                    counts[2] += 1
                    continue
                cert = branch["bounds"][obj]
                endpoint = F(cert["range"][0 if side == "lower" else 1])
                lhs, rhs = conclusion.split(" ≤ ")
                linear_part, constant = (rhs, lhs) if side == "lower" else (lhs, rhs)
                assert linear(linear_part) == (OBJECTIVES[obj], 0)
                assert value(constant, {}) == endpoint
                counts[0] += 1
                attained = name + "_attained"
                expected_names.add(attained)
                formula = blocks[attained].split(" := by", 1)[0].strip()[1:].strip()
                assertions = [s.strip()[1:-1] for s in formula.split(" ∧")]
                assert len(assertions) == len(rows) + 4
                point = tuple(map(F, cert[side + "_witness"]))
                for i, clause in enumerate(assertions[: len(rows)]):
                    left, right = clause.split(" ≤ ")
                    assert value(left, {}) == sum(
                        a * b for a, b in zip(rows[i][0], point, strict=True)
                    )
                    assert value(right, {}) == rows[i][1]
                    assert value(left, {}) <= value(right, {})
                left, right = assertions[-4].split(" = ")
                assert (
                    value(left, {})
                    == sum(a * b for a, b in zip(OBJECTIVES[obj], point, strict=True))
                    == endpoint
                    == value(right, {})
                )
                lam = point[2] / point[1] if point[1] else F(1, 5)
                for clause, expected in zip(
                    assertions[-3:-1], ((F(1, 5), lam), (lam, F(3, 10))), strict=True
                ):
                    left, right = clause.split(" ≤ ")
                    assert (value(left, {}), value(right, {})) == expected
                    assert expected[0] <= expected[1]
                left, right = assertions[-1].split(" = ")
                assert value(left, {}) == point[2] == value(right, {}) == lam * point[1]
                counts[1] += 1
    assert set(blocks) == expected_names and counts == [56, 56, 1]
    return counts


def main():
    text = (HERE / "domain_source_bounds.lean").read_text()
    counts = audit(text)
    changes = {
        "hypothesis_coefficient": text.replace(
            "(h0 : (1 / 1 : ℝ) * (w)", "(h0 : (2 / 1 : ℝ) * (w)", 1
        ),
        "bound_endpoint": text.replace(": (-11 / 10 : ℝ) ≤", ": (-12 / 10 : ℝ) ≤", 1),
        "witness_value": text.replace("((-11 / 10 : ℝ))", "((-12 / 10 : ℝ))", 1),
        "omitted_declaration": text.replace(
            "theorem baseline_nonnegative_d_wheel_lower ", "private lemma omitted ", 1
        ),
    }
    rejected = []
    for label, changed in changes.items():
        assert changed != text
        try:
            audit(changed)
        except (AssertionError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(label)
    data = {
        "counts": counts,
        "negative_controls_rejected": rejected,
        "lean_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "source_sha256": {
            name: hashlib.sha256((SRC / name).read_bytes()).hexdigest()
            for name in ("model.json", "results.json")
        },
        "scope": "Independent parse and rational evaluation of literal statements against frozen original model/results; not a kernel proof of JSON parser or source identity.",
    }
    (HERE / "critic_literal_binding.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
