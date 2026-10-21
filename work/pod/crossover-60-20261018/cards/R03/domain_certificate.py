"""Bind a trusted checker receipt to complete candidate payload; no cryptographic claim."""

import json
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from pathlib import Path

from domain_transaction import Candidate, Snapshot, Timing, atomic_step


@dataclass(frozen=True)
class TrustedReceipt:
    # Only a correct source checker may issue this value: not enforced by Python typing.
    payload: tuple


def payload(candidate):
    return candidate.snapshot, candidate.execution, candidate.delta


def receipt_step(candidate, receipt, live, timing):
    if payload(candidate) != receipt.payload:
        return live, "certificate-payload-reject"
    return atomic_step(candidate, live, timing)


def main():
    base = Snapshot()
    candidate = Candidate(base)
    timing = Timing()
    receipt = TrustedReceipt(payload(candidate))
    # This token is assumed to be issued by the original correct source checker.
    assert receipt_step(candidate, receipt, base, timing)[1] == "accepted"
    mutations = {
        "delta": replace(candidate, delta=Q(1)),
        "execution": replace(candidate, execution=Q(7, 10)),
        "snapshot_goal": replace(candidate, snapshot=replace(base, task=(Q(1),) + base.task[1:])),
    }
    results = {}
    for name, damaged in mutations.items():
        result = receipt_step(damaged, receipt, damaged.snapshot, timing)
        assert result == (damaged.snapshot, "certificate-payload-reject")
        results[name] = result[1]
    # Preserve first-model failure explicitly: a Boolean alone is not payload binding.
    bad = mutations["delta"]
    original_next, original_status = atomic_step(bad, base, timing)
    assert original_status == "accepted"
    original_target = original_next.offset + sum(delta for _, delta in original_next.events)
    assert original_target == Q(51, 50) != base.task[0]
    out = {
        "payload_mutations": results,
        "original_boolean_model_mutated_target": str(original_target),
        "scope": "Exact in-memory receipt equality; correct issuance and integrity of trusted receipt are premises. It is not a signature, remote attestation, or source certificate re-evaluation.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out))


if __name__ == "__main__":
    main()
