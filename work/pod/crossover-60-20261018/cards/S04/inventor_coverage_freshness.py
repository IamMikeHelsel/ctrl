"""Exact negative controls for coverage summaries and unanchored freshness."""

import copy
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions required")

expected = [i for i in range(16) if i.bit_count() % 2 == 0]
wrong = [i for i in range(16) if i.bit_count() % 2 == 1]


def syndrome(indices):
    return [sum(i**power for i in indices) for power in range(4)]


assert syndrome(expected) == syndrome(wrong)
assert set(expected).isdisjoint(wrong)
assert len(expected) == len(wrong) == 8
assert set(expected) != set(wrong)
# A summary-only checker accepts all four equal aggregate checks; exact coverage rejects.
assert syndrome(wrong) == syndrome(expected)
complete_accepts_wrong = set(wrong) == set(expected)
assert not complete_accepts_wrong

model = {"declared_model": "fixed scalar theorem", "required_cases": expected}
model_blob = json.dumps(model, sort_keys=True).encode()
model_digest = hashlib.sha256(model_blob).hexdigest()
receipt = {
    "model_digest": model_digest,
    "case_ids": expected,
    "epoch": 17,
    "producer_says_generated_now": True,
}


def local_check(candidate):
    return candidate["model_digest"] == model_digest and set(candidate["case_ids"]) == set(expected)


def context_check(candidate, authoritative_epoch):
    return local_check(candidate) and candidate["epoch"] == authoritative_epoch


# WorldA: epoch17 is current. WorldB: current epoch18, but all local checker inputs
# are the same replayed epoch17 bytes. No function of those bytes can distinguish.
world_a_input = json.dumps(receipt, sort_keys=True).encode()
world_b_input = json.dumps(receipt, sort_keys=True).encode()
assert world_a_input == world_b_input
assert local_check(receipt)
assert context_check(receipt, 17)
assert not context_check(receipt, 18)
# A producer-controlled freshness label is not an external anchor.
relabelled = copy.deepcopy(receipt)
relabelled["epoch"] = 18
assert context_check(relabelled, 18)
# This does not prove new mathematical generation. For unchanged model/cases,
# reusing a valid proof may be entirely legitimate; policy must say what is fresh.
assert relabelled["model_digest"] == receipt["model_digest"]
out = {
    "status": "pass",
    "coverage": {
        "expected_cases": expected,
        "wrong_cases": wrong,
        "equal_moments_0_through_3": syndrome(expected),
        "exact_set_rejects_wrong": not complete_accepts_wrong,
    },
    "freshness": {
        "identical_local_bytes_in_two_worlds": True,
        "old_receipt_passes_local_math_check": local_check(receipt),
        "authoritative_epoch_rejects_replay": not context_check(receipt, 18),
        "producer_relabelling_does_not_prove_regeneration": True,
    },
    "boundary": "Finite exact counterexamples plus indistinguishability argument. "
    "The original checker already uses exact sets, not these weak moments. "
    "External epoch integrity/authentication and proof/model binding are "
    "separate obligations; a cached proof can remain valid.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
