"""Serialize fixed source certificate statements; Lean checks every emitted proof."""

import hashlib
import importlib.util
import json
from fractions import Fraction as F
from pathlib import Path

CARD = Path(__file__).resolve().parent
ROOT = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution"
)
spec = importlib.util.spec_from_file_location("bounds_checker", ROOT / "check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
m = json.loads((ROOT / "model.json").read_text())
r = json.loads((ROOT / "results.json").read_text())
assert hashlib.sha256((ROOT / "model.json").read_bytes()).hexdigest() == checker.MODEL_SHA256
assert checker.verify(r, m) == (56, 1, 8)


def rat(raw):
    q = F(raw)
    return f"({q.numerator} / {q.denominator} : ℝ)"


def dot(a, values=("w", "d", "q")):
    terms = [f"{rat(c)} * ({v})" for c, v in zip(a, values, strict=True) if F(c)]
    return " + ".join(terms) or "(0 : ℝ)"


lines = [
    "import Mathlib.Data.Real.Basic",
    "import Mathlib.Tactic.Linarith",
    "import Mathlib.Tactic.NormNum",
    "namespace CampaignS04Source",
]
names = []
binding = []
for stage in sorted(checker.STAGES):
    for sign in sorted(checker.SIGNS):
        b = r["stages"][stage]["branches"][sign]
        rows = b["constraints"]
        actual = {(tuple(map(F, z["a"])), F(z["b"])) for z in rows}
        assert actual == checker.expected(m, stage, sign)
        prefix = stage + "_" + sign
        hypotheses = "\n".join(
            f"    (h{i} : {dot(z['a'])} ≤ {rat(z['b'])})" for i, z in enumerate(rows)
        )
        if not b["feasible"]:
            name = prefix + "_empty"
            used = ", ".join("h" + str(t["constraint"]) for t in b["farkas"])
            lines.append(
                f"theorem {name} (w d q : ℝ)\n{hypotheses} : False := by\n  linarith only [{used}]"
            )
            names.append(name)
            binding.append({"name": name, "stage": stage, "sign": sign, "kind": "infeasible"})
            continue
        for objective, a in checker.OBJECTIVES.items():
            cert = b["bounds"][objective]
            for side, index in [("lower", 0), ("upper", 1)]:
                val = cert["range"][index]
                name = prefix + "_" + objective + "_" + side
                lhs, rhs = (rat(val), dot(a)) if side == "lower" else (dot(a), rat(val))
                dual = cert[
                    "lower_dual_for_negative_objective" if side == "lower" else "upper_dual"
                ]
                used = ", ".join("h" + str(t["constraint"]) for t in dual)
                lines.append(
                    f"theorem {name} (w d q : ℝ)\n{hypotheses} : {lhs} ≤ {rhs} := by\n  linarith only [{used}]"
                )
                names.append(name)
                witness = cert[side + "_witness"]
                values = tuple(map(rat, witness))
                assertions = [f"({dot(z['a'], values)} ≤ {rat(z['b'])})" for z in rows]
                assertions.append(f"({dot(a, values)} = {rat(val)})")
                d, q = F(witness[1]), F(witness[2])
                lam = q / d if d else F(1, 5)
                assertions.extend(
                    [
                        f"({rat(F(1, 5))} ≤ {rat(lam)})",
                        f"({rat(lam)} ≤ {rat(F(3, 10))})",
                        f"({rat(q)} = {rat(lam)} * {rat(d)})",
                    ]
                )
                witness_name = name + "_attained"
                lines.append(
                    f"theorem {witness_name} :\n    "
                    + " ∧\n    ".join(assertions)
                    + " := by norm_num"
                )
                names.append(witness_name)
                binding.append(
                    {
                        "name": name,
                        "attainment": witness_name,
                        "stage": stage,
                        "sign": sign,
                        "objective": objective,
                        "side": side,
                        "value": val,
                        "witness": witness,
                    }
                )
lines.append("end CampaignS04Source")
lines.extend("#print axioms CampaignS04Source." + name for name in names)
source_hashes = {
    p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
    for p in ["model.json", "results.json", "check.py"]
}
lines.insert(
    0, "/- Literal fixed-source certificates. Source hashes: " + json.dumps(source_hashes) + " -/"
)
source = "\n\n".join(lines) + "\n"
(CARD / "domain_source_bounds.lean").write_text(source)
manifest = {
    "source_sha256": source_hashes,
    "generated_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "declarations": len(names),
    "bound_certificates": 56,
    "attainment_certificates": 56,
    "infeasibility_certificates": 1,
    "binding": binding,
    "limit": "Generator/model parsing is not kernel verified; inspect literal inequalities and external source binding.",
}
(CARD / "domain_source_bounds_binding.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(f"Emitted {len(names)} declarations.")
