"""Independent authority-binding replay and missing jerk-admission bridge witness."""

import hashlib
import json
import runpy
import sys
from dataclasses import replace
from fractions import Fraction as F
from math import comb
from pathlib import Path

P = Path(__file__).parent
sys.path.insert(0, str(P))
# Preserve the exact tested wrapper without modifying the producer.
snapshot = P / "critic_binding_snapshot.py.snapshot"
if not snapshot.exists():
    snapshot.write_bytes((P / "pm_binding.py").read_bytes())
source = snapshot.read_bytes()
m = runpy.run_path(str(P / "critic_binding_snapshot.py.snapshot"), run_name="critic_import")
Commit, Event, State, append, bound = [
    m[k] for k in ["Commit", "Event", "State", "append", "bound_append"]
]
c = Commit(1, 1, F(1, 1000), F(3, 2), F(1, 5), (), Event(F(11, 50), F(1, 1000)))
receipt = (1, 1, F(1, 1000), F(3, 2), F(1, 5))
fake = replace(c, goal=F(2, 1000), event=replace(c.event, delta=F(2, 1000)))
assert append(State(), fake)[1] == "appended"
assert bound(State(), fake, receipt, F(1, 5))[1] == "authority_binding_rejected"
assert bound(State(), c, receipt, F(2))[1] == "causality_rejected"
s, status = bound(State(), c, receipt, F(1, 5))
assert status == "appended"
assert bound(State(), fake, (1, 1, F(2, 1000), F(3, 2), F(1, 5)), F(1, 5))[1] == "appended"
late_duplicate, late_status = bound(s, c, receipt, F(2))
assert late_duplicate == s

# Exact original jerk guard is a separate obligation, not implied by this wrapper.
large = replace(c, goal=F(1, 25), event=replace(c.event, delta=F(1, 25)))
large_receipt = (1, 1, F(1, 25), F(3, 2), F(1, 5))
large_state, large_status = bound(State(), large, large_receipt, F(1, 5))
assert large_status == "appended"
# At normalized time2, F'''(2)=-2. Units are metres and seconds.
f3 = sum((-1) ** i * comb(4, i) * max(F(2) - i, 0) for i in range(5))
assert f3 == -2
peak = abs(large.event.delta * f3 / large.h**3)
assert peak == 10 > F(15, 2)
maximum_delta = F(15, 2) * large.h**3 / 2
assert maximum_delta == F(3, 100)
# Threshold negative controls: exact30mm meets the isolated guard;31mm violates it.
assert 2 * F(3, 100) / large.h**3 == F(15, 2)
assert 2 * F(31, 1000) / large.h**3 > F(15, 2)
# The original isolated theorem requires old-tail completion by ISSUE time,
# not merely by the new scheduled execution. This request arrives mid-motion.
next_c = Commit(1, 2, F(2, 1000), F(3), F(1, 5), s.history, Event(F(3, 2), F(1, 1000)))
issue = F(1, 2)
old_tail_end = c.event.time + 4 * c.h
assert issue < old_tail_end == F(51, 50) < next_c.event.time
assert bound(s, next_c, (1, 2, F(2, 1000), F(3), F(1, 5)), issue)[1] == "appended"
# External old-history validity is also absent: the relation assumes supplied
# state came from valid previous commits; it is not a history-recovery verifier.
out = {
    "wrapper_sha256": hashlib.sha256(source).hexdigest(),
    "five_binding_cases": "passed",
    "midmove_issue_accepted_but_source_premise_fails": True,
    "issue_old_tail_new_execution": [str(issue), str(old_tail_end), str(next_c.event.time)],
    "late_identical_retry_status": late_status,
    "large_authorized_delta_m": "1/25",
    "wrapper_large_status": large_status,
    "exact_peak_jerk_m_per_s3": str(peak),
    "frozen_jerk_limit_m_per_s3": "15/2",
    "isolated_maximum_delta_m": str(maximum_delta),
    "scope": "Missing admission-premise counterexample for static interface composition, not physical trajectory or existing source theorem refutation.",
}
(P / "critic_binding_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
