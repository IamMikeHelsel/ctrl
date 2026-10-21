"""Independent exact reconstruction from frozen four-box signed-event equations.
No source imports, physical simulation, history reset, or native-plan regeneration.
"""

import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

H = F(1, 5)
COEFF = (1, -4, 6, -4, 1)
ROOT = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/moving-goal-08/builder"
)
spec = json.loads((SOURCE / "packets.json").read_text())


def derivative(events, time, order):
    return sum(
        delta
        * coefficient
        * max(time - tau - i * H, F(0)) ** (4 - order)
        / factorial(4 - order)
        / H**4
        for tau, delta in events
        for i, coefficient in enumerate(COEFF)
    )


def pieces(events, now):
    knots = sorted(
        {now} | {tau + i * H for tau, _ in events for i in range(5) if tau + i * H >= now}
    )
    out = []
    for left, right in zip(knots, knots[1:], strict=False):
        middle = (left + right) / 2
        ds = [
            sum(
                delta
                * coefficient
                * (left - tau - i * H) ** (4 - order)
                / factorial(4 - order)
                / H**4
                for tau, delta in events
                for i, coefficient in enumerate(COEFF)
                if tau + i * H < middle
            )
            for order in range(5)
        ]
        out.append((left, right, ds))
    return out


def bounds(events, now):
    poly = pieces(events, now)
    a_values, j_values = [], []
    velocity_bernstein = []
    encoded = []
    for left, right, ds in poly:
        width = right - left
        a_nodes = {F(0), width}
        if ds[4] and 0 < -ds[3] / ds[4] < width:
            a_nodes.add(-ds[3] / ds[4])
        a_values.extend((abs(ds[2] + ds[3] * u + ds[4] * u**2 / 2), left + u) for u in a_nodes)
        j_values.extend((abs(ds[3] + ds[4] * u), left + u) for u in (F(0), width))
        mono = [ds[1 + k] * width**k / factorial(k) for k in range(4)]
        bern = [sum(mono[k] * F(comb(i, k), comb(3, k)) for k in range(i + 1)) for i in range(4)]
        velocity_bernstein.extend(map(abs, bern))
        encoded.append(
            {
                "left": str(left),
                "right": str(right),
                "derivatives": list(map(str, ds)),
                "velocity_bernstein": list(map(str, bern)),
            }
        )
    a_peak, a_time = max(a_values, default=(F(0), now))
    j_peak, j_time = max(j_values, default=(F(0), now))
    v_upper = max(velocity_bernstein, default=F(0))
    return {
        "velocity_sufficient_upper": str(v_upper),
        "acceleration_exact_peak": str(a_peak),
        "acceleration_witness_time": str(a_time),
        "jerk_exact_peak": str(j_peak),
        "jerk_witness_time": str(j_time),
        "VAJ_pass": v_upper <= F(1, 10) and a_peak <= F(1, 2) and j_peak <= F(15, 2),
        "pieces": encoded,
    }


rows = []
for case in spec["cases"]:
    events = []
    previous_goal = F(0)
    for packet in case["packets"]:
        ready = F(packet["ready_s"])
        admission = -(-ready // F(1, 50)) * F(1, 50)
        execution = admission + F(case["buffer_s"])
        delta = F(packet["target_m"]) - previous_goal
        candidate = events + [(execution, delta)]
        check = bounds(candidate, admission)
        jerk_pass = F(check["jerk_exact_peak"]) <= F(15, 2)
        deadline = F(case["deadline_s"])
        tail = max(t for t, _ in candidate) + 4 * H
        rows.append(
            {
                "case": case["id"],
                "sequence": packet["sequence"],
                "admission": str(admission),
                "execution": str(execution),
                "candidate_events": [[str(t), str(d)] for t, d in candidate],
                "jerk_only_pass": jerk_pass,
                "reference_tail": str(tail),
                "deadline": str(deadline),
                "causal_deadline_pass": execution <= deadline,
                "full_tail_before_deadline": tail <= deadline,
                **check,
            }
        )
        # Reproduce source jerk-only admission; do not silently replace its accepted history.
        if jerk_pass:
            events, previous_goal = candidate, F(packet["target_m"])
    rows[-1]["source_retained_events"] = [[str(t), str(d)] for t, d in events]
    rows[-1]["source_final_accepted_goal"] = str(previous_goal)

second = {row["case"]: row for row in rows if row["sequence"] == 101}
assert second["return_generous"]["acceleration_exact_peak"] == "21/32"
assert second["return_generous"]["jerk_exact_peak"] == "25/4"
assert second["reverse_far_guard"]["jerk_exact_peak"] == "45/4"
assert second["reverse_far_guard"]["source_final_accepted_goal"] == "1/50"
assert not second["return_generous"]["VAJ_pass"]
assert second["return_late_buffered"]["VAJ_pass"]
assert not second["return_predelivery"]["causal_deadline_pass"]
(ROOT / "domain_fir_results.json").write_text(json.dumps(rows, indent=2) + "\n")
for row in second.values():
    print(json.dumps({key: val for key, val in row.items() if key != "pieces"}))

# Positive all-time reference certificate for source buffered case only.
# Every derivative of orders1..3 is degree<=3 on each complete-history knot interval.
# Express all of them in cubic Bernstein form (degree elevation for A/J).
buffered_events = [(F(7, 25), F(1, 50)), (F(17, 25), -F(1, 50))]
limits = {1: F(1, 10), 2: F(1, 2), 3: F(15, 2)}
certificates = []
for left, right, ds in pieces(buffered_events, F(0)):
    width = right - left
    for order, limit in limits.items():
        mono = [
            ds[order + k] * width**k / factorial(k) if order + k <= 4 else F(0) for k in range(4)
        ]
        bern = [sum(mono[k] * F(comb(i, k), comb(3, k)) for k in range(i + 1)) for i in range(4)]
        assert all(abs(b) <= limit for b in bern)
        certificates.append(
            {
                "left": str(left),
                "right": str(right),
                "order": order,
                "power_coefficients": list(map(str, mono)),
                "bernstein_coefficients": list(map(str, bern)),
                "limit": str(limit),
            }
        )
assert all(derivative(buffered_events, F(2), order) == 0 for order in (1, 2, 3))
(ROOT / "domain_buffered_certificate.json").write_text(json.dumps(certificates, indent=2) + "\n")
print("buffered exact cubic Bernstein certificates", len(certificates))
