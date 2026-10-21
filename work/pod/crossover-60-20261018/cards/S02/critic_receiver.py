"""Exercise the final prototype receiver's actual consumer entrypoint."""

import hashlib
import importlib.util
import json
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
path = HERE / "inventor_release.py"
spec = importlib.util.spec_from_file_location("release_candidate", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
h = module.H
count = 0
for delays in product((0, h / 2, h), repeat=5):
    ids = list(range(630, 635))
    arrivals = [i * h + d for i, d in zip(ids, delays, strict=True)]
    released, size = module.consume(ids, arrivals, 630, 5)
    assert released == ids and size <= 2
    count += 1
cases = [
    ([632], [631 * h], 632, 1, h, True),
    ([632, 634], [633 * h, 635 * h], 632, 3, h, True),
    ([632, 632], [633 * h, 633 * h], 632, 1, h, True),
    ([631], [632 * h], 632, 1, h, True),
    ([632], [633 * h], 632, 1, h, False),
    ([632], [633 * h + h / 10], 632, 1, h, True),
]
rejected = []
for args in cases:
    try:
        module.consume(*args)
    except ValueError as exc:
        rejected.append(str(exc))
    else:
        raise AssertionError(args)
result = {
    "producer_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    "positive_patterns": count,
    "rejected_controls": rejected,
    "remaining_scope": "Trusted expected acquisition interval; actual packet payload and timestamp not represented; no runtime refinement proof.",
}
(HERE / "critic_release_final.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
