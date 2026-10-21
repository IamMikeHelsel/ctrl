"""New-event-only FIR width candidates; exact reference V/A/J and deadline gates."""

import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

HERE = Path(__file__).parent
COEFF = [1, -4, 6, -4, 1]
LIMITS = {1: F(1, 10), 2: F(1, 2), 3: F(15, 2)}
FIRST = (F(11, 50), F(1, 50), F(1, 5))
REVISION = F(13, 25)


def at(events, t, order):
    return sum(
        (
            delta * c * max(t - tau - i * h, F(0)) ** (4 - order) / F(factorial(4 - order)) / h**4
            for tau, delta, h in events
            for i, c in enumerate(COEFF)
        ),
        F(0),
    )


def pieces(events, end=F(5, 2), extra=()):
    knots = sorted(
        {F(0), end, *extra}
        | {tau + i * h for tau, _, h in events for i in range(5) if 0 <= tau + i * h <= end}
    )
    answer = []
    for left, right in zip(knots, knots[1:], strict=False):
        mid = (left + right) / 2
        ds = [
            sum(
                (
                    delta * c * (left - tau - i * h) ** (4 - order) / F(factorial(4 - order)) / h**4
                    for tau, delta, h in events
                    for i, c in enumerate(COEFF)
                    if tau + i * h < mid
                ),
                F(0),
            )
            for order in range(5)
        ]
        answer.append((left, right, ds))
    return answer


def evaluate(ds, s, order):
    return sum(ds[order + k] * s**k / F(factorial(k)) for k in range(5 - order))


def bernstein(ds, width, order):
    coefficients = [ds[order + k] * width**k / F(factorial(k)) for k in range(5 - order)]
    degree = len(coefficients) - 1
    return [
        sum(coefficients[k] * F(comb(i, k), comb(degree, k)) for k in range(i + 1))
        for i in range(degree + 1)
    ]


def inspect(name, delta, newwidth, deadline):
    events = [FIRST, (REVISION, delta, newwidth)]
    phases = pieces(events, extra=(deadline, F(1, 2)))
    for (left, right, ds), (next_left, _, next_ds) in zip(phases, phases[1:], strict=False):
        assert right == next_left
        assert all(evaluate(ds, right - left, k) == next_ds[k] for k in range(4))
    peak_a = (F(0), F(0))
    peak_j = (F(0), F(0))
    velocity_bounds = []
    certificates = []
    for left, right, ds in phases:
        width = right - left
        roots = [F(0), width]
        if ds[4] != 0:
            stationary = -ds[3] / ds[4]
            if 0 < stationary < width:
                roots.append(stationary)
        for s in roots:
            a = evaluate(ds, s, 2)
            if abs(a) > abs(peak_a[1]):
                peak_a = (left + s, a)
        for s in [F(0), width]:
            j = evaluate(ds, s, 3)
            if abs(j) > abs(peak_j[1]):
                peak_j = (left + s, j)
        vb = bernstein(ds, width, 1)
        velocity_bounds.extend(vb)
        certificates.append(
            {
                "start": left,
                "end": right,
                "derivatives": ds,
                "derivative_order": "q,qv,qa,j,snap at start; local polynomial uses derivative[k]*s^k/k!",
                "velocity_bernstein": vb,
                "acceleration_extremum_offsets": roots,
            }
        )
    peak_v_bound = max(map(abs, velocity_bounds))
    old_tail = FIRST[0] + 4 * FIRST[2]
    new_tail = REVISION + 4 * newwidth
    final_tail = max(old_tail, new_tail)
    endpoint = [at(events, deadline, k) for k in range(4)]
    # Exact local starting derivatives of the new event vanish through jerk.
    for k in range(4):
        assert at(events, REVISION, k) == at([FIRST], REVISION, k)
    before = [F(0), F(1, 5), FIRST[0], F(1, 2), REVISION]
    assert all(at(events, t, k) == at([FIRST], t, k) for t in before for k in range(4))
    if deadline >= final_tail:
        assert endpoint == [sum(d for _, d, _ in events), F(0), F(0), F(0)]
    assert phases[-1][2] == [sum(d for _, d, _ in events), F(0), F(0), F(0), F(0)]
    passed = (
        peak_v_bound <= LIMITS[1] and abs(peak_a[1]) <= LIMITS[2] and abs(peak_j[1]) <= LIMITS[3]
    )
    return {
        "name": name,
        "events": events,
        "deadline": deadline,
        "final_tail": final_tail,
        "deadline_reference_state_q_v_a_j": endpoint,
        "velocity_sufficient_bound": peak_v_bound,
        "acceleration_exact_peak": peak_a,
        "jerk_exact_peak": peak_j,
        "reference_VAJ_pass": passed,
        "tail_before_deadline": final_tail <= deadline,
        "full_reference_contract_pass": passed and final_tail <= deadline,
        "piece_certificates": certificates,
    }


cases = [
    inspect("frozen_return", -F(1, 50), F(1, 5), F(17, 10)),
    inspect("return_widen_new_only", -F(1, 50), F(1, 4), F(17, 10)),
    inspect("frozen_far_proposal", -F(1, 25), F(1, 5), F(19, 10)),
    inspect("far_widen_new_only", -F(1, 25), F(3, 10), F(19, 10)),
]
assert abs(cases[0]["acceleration_exact_peak"][1]) == F(21, 32)
assert abs(cases[2]["jerk_exact_peak"][1]) == F(45, 4)
result = {
    "cases": cases,
    "limits": LIMITS,
    "scope": "Reference-only exact rational polynomial tests for explicit new candidates. Old event widths/times/deltas unchanged, no actual-state reset, task deadlines unchanged. Bernstein velocity enclosure is sufficient, not necessarily tight. Frozen far proposal was rejected in original benchmark; its two-event curve here is counterfactual guard input, not executed baseline. No physical endpoint or effort verdict.",
}


def encode(v):
    if isinstance(v, F):
        return str(v)
    if isinstance(v, (list, tuple)):
        return [encode(x) for x in v]
    if isinstance(v, dict):
        return {str(k): encode(x) for k, x in v.items()}
    return v


(HERE / "inventor_width.json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(
    json.dumps(
        encode(
            [
                {k: v for k, v in case.items() if k not in ["piece_certificates", "events"]}
                for case in cases
            ]
        ),
        indent=2,
    )
)
