"""Independent caller probes for the exact payload receipt boundary."""

import json
from dataclasses import replace
from fractions import Fraction as F
from pathlib import Path
import runpy
import sys

P = Path(__file__).resolve().parent
sys.path.insert(0, str(P))
m = runpy.run_path(str(P / "domain_certificate.py"), run_name="audit_receipt")
s = m["Snapshot"]()
p = m["Candidate"](s)
t = m["Timing"]()
receipt = m["TrustedReceipt"](m["payload"](p))
assert m["receipt_step"](p, receipt, s, t)[1] == "accepted"
mutations = [
    replace(p, delta=F(1)),
    replace(p, execution=F(7, 10)),
    replace(p, snapshot=replace(s, task=(F(1),) + s.task[1:])),
]
for q in mutations:
    assert m["receipt_step"](q, receipt, q.snapshot, t)[1] == "certificate-payload-reject"
# Deliberate untrusted issuance is outside the prototype's stated premise.
bad = mutations[0]
forged = m["TrustedReceipt"](m["payload"](bad))
assert m["receipt_step"](bad, forged, s, t)[1] == "accepted"
out = {
    "original_receipt_positive": True,
    "three_payload_mutations_rejected": True,
    "untrusted_issuance_accepts": True,
    "scope": "Correct receipt issuance and integrity remain trusted. Exact payload equality is checked; actual source certificate, candidate list/checker version, serialization and remote authenticity are not established.",
}
(P / "critic_receipt.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
