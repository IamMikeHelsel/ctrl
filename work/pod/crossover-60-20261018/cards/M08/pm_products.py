"""Finite declared bracket-choice audit. Source does not uniquely bind C/J/J."""

import importlib.util
import json
from itertools import product
from pathlib import Path

P = Path(__file__).parent
spec = importlib.util.spec_from_file_location("hodge", P / "pm_hodge_basis.py")
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)


def combine(a, b, alpha=1):
    out = a.copy()
    for k, v in b.items():
        h.add(out, k, alpha * v)
    return out


def choice(xi, first, inner, outer):
    sx = h.star(xi)
    t1 = h.wedge_bracket(h.PHI1, sx, -1 if first == "C" else 1)
    # All our Riemann fixtures have zero vector Jordan contraction.
    if first == "J":
        assert not t1
    q = h.star(h.wedge_bracket(h.PHI2, sx, -1 if inner == "C" else 1))
    t2 = h.star(h.wedge_bracket(h.PHI1, q, -1 if outer == "C" else 1))
    phase = (inner == "J") + (outer == "J")
    if phase % 2:
        assert not t2
    real_factor = 1 if phase == 0 else -1
    return h.star(combine({k: 2 * v for k, v in t1.items()}, t2, -real_factor))


xi = {(3, 3): 1}  # Single positive sectional R0101=1, canonical spin normalization.
target = {k: -v for k, v in h.component_twice(0, 1, 3).items()}
rows = {}
for choices in product("CJ", repeat=3):
    result = choice(xi, *choices)
    rows["".join(choices)] = {
        "matches_declared_E_bridge": result == target,
        "rows": {str(k): str(v) for k, v in result.items()},
    }
assert [k for k, v in rows.items() if v["matches_declared_E_bridge"]] == ["CJJ"]
# Pure Ricci and Einstein supports are disjoint on this fixture: no global rescaling repairs CCC.
ccc = choice(xi, "C", "C", "C")
assert ccc and target and not (set(ccc) & set(target))
out = {
    "fixture": "positive sectional01, R0101=1; outputs twice Hodge-identified source nesting",
    "choices": rows,
    "global_rescale_repairs_CCC": False,
    "scope": "Within fixed canonical Phi normalization and the8 C/J choices, onlyCJJ matches target; not proof of author-selected interpretation or all invariant operator families.",
}
(P / "pm_products.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "matching_choices": [k for k, v in rows.items() if v["matches_declared_E_bridge"]],
            "ccc_support": len(ccc),
            "target_support": len(target),
        }
    )
)
