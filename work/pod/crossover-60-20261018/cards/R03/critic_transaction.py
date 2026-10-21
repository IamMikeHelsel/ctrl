"""Independent bounded transition audit and certificate-payload negative."""

import json
from dataclasses import replace
from fractions import Fraction as F
from pathlib import Path
import runpy

P = Path(__file__).resolve().parent
m = runpy.run_path(str(P / "domain_transaction.py"), run_name="independent_audit")
base = m["Snapshot"]()
p = m["Candidate"](base)
t = m["Timing"]()
step = m["atomic_step"]
positive, status = step(p, base, t)
assert status == "accepted" and positive.events == base.events + ((F(31, 50), F(-1, 50)),)
assert positive.history_version == base.history_version + 1
assert step(p, positive, t)[0] == positive
for age, expected in [(F(35, 1000), True), (F(36, 1000), False)]:
    tt = replace(t, read_age=age)
    direct = (
        tt.estimate
        + tt.commit_clock_error
        + tt.execution_clock_error
        + tt.read_age
        + tt.publication_tail
        + tt.dispatch
        <= p.execution
    )
    assert direct == expected == m["ordering"](p, tt)
# The bool abstracts a dependent certificate; it is not a secure entrypoint.
bad = replace(p, delta=F(1), checked_certificate=True)
next_bad, status_bad = step(bad, base, t)
final = next_bad.offset + sum(d for _, d in next_bad.events)
assert status_bad == "accepted" and final != base.task[0]
negative_time = replace(t, publication_tail=F(-1, 1000))
assert step(p, base, negative_time)[1] == "time-reject"
out = {
    "typed_positive_and_duplicate": True,
    "boundary_35ms_accept_36ms_reject": True,
    "negative_budget_rejected": True,
    "unbound_checked_bool_probe": {
        "status": status_bad,
        "final_target": str(final),
        "task_goal": str(base.task[0]),
    },
    "scope": "Model explicitly assumes an already checked candidate; mutated bool witness demonstrates that a production consumer must bind certificate to exact payload. It is not a refutation of the abstract checked-certificate assumption.",
}
(P / "critic_transaction.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
