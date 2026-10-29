#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["sympy==1.14.0"]
# ///
"""Eight bounded math experiments; exact witnesses, explicit negative controls.

Run: uv run experiments/math_explainers/run.py
This is an experiment runner, not a theorem prover or a hardware safety check.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections import deque
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

import sympy as s

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "site/explainers/lab/results.json"
PIN = "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
OAI = f"https://github.com/openai/math/blob/{PIN}/lean/"
SOURCES = [
    {
        "id": "tao-equations",
        "title": "Terence Tao: The equational theories project, a brief tour",
        "url": "https://terrytao.wordpress.com/2024/10/12/the-equational-theories-project-a-brief-tour/",
        "date": "2024-10-12",
        "use": "Method inspiration: search finite countermodels before trusting an algebraic rewrite.",
    },
    {
        "id": "tao-sumsets",
        "title": "Green, Manners and Tao: Sumsets and entropy revisited",
        "url": "https://terrytao.wordpress.com/2023/06/27/sumsets-and-entropy-revisited/",
        "date": "2023-06-27",
        "use": "Method inspiration: inspect additive support growth and distinguish support from entropy. No application of PFR is claimed.",
    },
    {
        "id": "tao-blueprint",
        "title": "Terence Tao: Formalizing PFR in Lean4 using Blueprint",
        "url": "https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/",
        "date": "2023-11-18",
        "use": "Presentation inspiration: expose dependencies and missing obligations.",
    },
    {
        "id": "oai-tropical",
        "title": "OpenAI/math: TruffetModel and TruffetCounterexample",
        "url": OAI + "OAI/Optimization/Tropical/TruffetCounterexample.lean",
        "model_url": OAI + "OAI/Optimization/Tropical/TruffetModel.lean",
        "commit": PIN,
        "date": "2026-10-26",
        "use": "Recompute the displayed feasible-point cost gap. The substitution algorithm and upstream Lean proof are not replayed by this suite.",
    },
    {
        "id": "oai-scheduling",
        "title": "OpenAI/math: ThreeMachine problem specification",
        "url": OAI + "ComparatorChallenges/ThreeMachine.lean",
        "commit": PIN,
        "date": "2026-10-26",
        "use": "Adopt the finite unit-job, precedence and three-machine model. Our tiny BFS is not the upstream algorithm or a replay of its complexity theorem.",
    },
    {
        "id": "ctrl-lyapunov",
        "title": "ctrl: DiscreteLyapunov",
        "url": "https://github.com/IamMikeHelsel/ctrl/blob/124e2f7787e31cf24f39e1a7b3bf37bf79a93df2/ControlsLean/Controls/DiscreteLyapunov.lean",
        "use": "Existing theorem context; new example arithmetic is checked separately.",
    },
    {
        "id": "ctrl-kalman",
        "title": "ctrl: ScalarKalman",
        "url": "https://github.com/IamMikeHelsel/ctrl/blob/124e2f7787e31cf24f39e1a7b3bf37bf79a93df2/ControlsLean/Estimation/ScalarKalman.lean",
        "use": "Existing theorem context; this experiment isolates the scalar quadratic objective.",
    },
    {
        "id": "ctrl-braking",
        "title": "ctrl: delayed braking study",
        "url": "https://iammikehelsel.github.io/ctrl/studies/latency-braking.html",
        "use": "Known constant-acceleration envelope; new sensitivity and boundary sweep.",
    },
]


def zero_check(expression):
    """Preserve SymPy's unknown outcome instead of treating it as success."""
    residual = s.simplify(expression)
    return {
        "residual": str(residual),
        "status": {True: "passed", False: "failed", None: "unknown"}[residual.is_zero],
    }


def require_zero(expression):
    check = zero_check(expression)
    if check["status"] != "passed":
        raise AssertionError(check)
    return check


def record(id, title, sources, question, scope, next_test, kill, **result):
    return dict(
        id=id,
        title=title,
        source_ids=sources,
        question=question,
        scope=scope,
        next_test=next_test,
        kill_criterion=kill,
        status="completed",
        **result,
    )


def lyapunov():
    a, x, p = s.symbols("a x p", real=True)
    identity = require_zero(p * x**2 - p * (a * x) ** 2 - p * (1 - a**2) * x**2)
    domain = s.solve_univariate_inequality(1 - a**2 > 0, a, relational=False)
    A = s.Matrix([[1, s.Rational(3, 5)], [-s.Rational(7, 20), s.Rational(3, 5)]])
    u, v, w = s.symbols("u v w")
    candidate = s.Matrix([[u, v], [v, w]])
    sol = s.solve(list(candidate - A.T * candidate * A - s.eye(2)), [u, v, w], dict=True)[0]
    P = candidate.subs(sol)
    checks = [require_zero(t) for t in P - A.T * P * A - s.eye(2)]
    assert P[0, 0] > 0 and P.det() > 0  # Sylvester, symmetric 2 x 2 only.
    points, state = [], s.Matrix([1, 0])
    for k in range(15):
        energy, norm2 = (state.T * P * state)[0], state.dot(state)
        points.append(
            {
                "k": k,
                "x": [str(t) for t in state],
                "energy": str(energy),
                "norm_squared": str(norm2),
                "display_energy": float(energy),
                "display_norm": math.sqrt(float(norm2)),
            }
        )
        state = A * state
    assert F(points[1]["norm_squared"]) > F(points[0]["norm_squared"])
    for before, after in zip(points, points[1:], strict=False):
        assert F(before["energy"]) - F(after["energy"]) == F(before["norm_squared"])
    scalar = []
    for numerator in range(-24, 25):
        rate = F(numerator, 20)
        scalar.append({"a": str(rate), "loss": str(1 - rate**2), "certificate": 1 - rate**2 > 0})
    return record(
        "lyapunov",
        "Length can grow while energy falls",
        ["ctrl-lyapunov"],
        "Can an exact certificate explain the transient that a norm plot hides?",
        "Exact rational example and CAS identities; no new kernel-checked theorem, rounding or plant model.",
        "Check rational certificates for a family of sampled closed-loop matrices with interval perturbations.",
        "Reject a candidate if P or P minus A-transpose P A loses positive definiteness.",
        evidence="CAS identity + exact rational replay",
        cases=len(scalar),
        conclusion="The first step increases squared length from 1 to 449/400 while energy drops by exactly 1.",
        checks=[identity, *checks],
        scalar_domain=str(domain),
        scalar=scalar,
        A=[[str(t) for t in A.row(i)] for i in range(2)],
        P=[[str(t) for t in P.row(i)] for i in range(2)],
        determinant=str(P.det()),
        samples=points,
        negative_control={"a": "11/10", "loss": "-21/100", "certificate": False},
    )


def stopping_distance(u, delay, accel, brake, error):
    if min(u, delay, accel, error) < 0 or brake <= 0:
        raise ValueError("nonnegative forward-motion inputs and positive braking required")
    return error + u * delay + accel * delay**2 / 2 + (u + accel * delay) ** 2 / (2 * brake)


def braking():
    u, t, A, b, e = s.symbols("u t A b e", nonnegative=True)
    D = e + u * t + A * t**2 / 2 + (u + A * t) ** 2 / (2 * b)
    sensitivity = s.factor(s.diff(D, t))
    require_zero(sensitivity - (u + A * t) * (1 + A / b))
    counts = {
        "cases": 0,
        "nominal_admits": 0,
        "nominal_false_admits": 0,
        "bounded_admits": 0,
        "bounded_false_admits": 0,
    }
    for speed, dv, delay, accel, brake, error in product(
        map(F, ["1/2", "1", "2"]),
        map(F, ["0", "1/10"]),
        map(F, ["0", "1/10", "1/4"]),
        map(F, ["0", "1", "2"]),
        map(F, ["1", "2", "4"]),
        map(F, ["0", "1/50"]),
    ):
        bound = stopping_distance(speed + dv, delay, accel, brake, error)
        # Independent phase integration using average endpoint velocities.
        v1 = speed + dv + accel * delay
        witness = error + ((speed + dv) + v1) * delay / 2 + v1 * (v1 / brake) / 2
        assert witness == bound
        for margin in map(F, ["-1/50", "0", "1/50"]):
            wall = bound + margin
            nominal = wall >= speed**2 / (2 * brake)
            bounded = wall >= bound
            counts["cases"] += 1
            counts["nominal_admits"] += nominal
            counts["nominal_false_admits"] += nominal and witness > wall
            counts["bounded_admits"] += bounded
            counts["bounded_false_admits"] += bounded and witness > wall
    assert counts["bounded_false_admits"] == 0 and counts["nominal_false_admits"] > 0
    args = (F("11/10"), F("1/5"), F(1), F(2), F("1/50"))
    bound = stopping_distance(*args)
    short = stopping_distance(args[0], F("9/50"), *args[2:])
    return record(
        "braking",
        "Delay consumes a calculable distance",
        ["ctrl-braking"],
        "How much clearance does a smaller delay buy under fixed bounds?",
        "A sharp 1D constant-acceleration model. Equality allows boundary contact. Rejection is not a stopping action.",
        "Replay measured timestamp-to-actuation traces with independently justified acceleration and braking bounds.",
        "Stop if any trace exceeds an assumed delay or braking bound; do not narrow bounds to improve admission rates.",
        evidence="CAS derivative + independent exact integration",
        **counts,
        conclusion=f"The bounded rule has no false admissions in {counts['cases']} constructed cases; the nominal rule has {counts['nominal_false_admits']}.",
        formula=str(D),
        latex=s.latex(D),
        sensitivity=str(sensitivity),
        example={
            "u": "11/10",
            "delay": "1/5",
            "accel": "1",
            "brake": "2",
            "error": "1/50",
            "distance": str(bound),
            "display_distance": float(bound),
            "delay_distance": str(args[0] * args[1] + args[2] * args[1] ** 2 / 2),
            "brake_distance": str((args[0] + args[2] * args[1]) ** 2 / (2 * args[3])),
            "saved_by_20ms": str(bound - short),
        },
        negative_control={
            "wall": "1/2",
            "understated_delay": "0",
            "reported_distance": str(stopping_distance(args[0], F(0), *args[2:])),
            "actual_distance": str(bound),
            "actual_crossing": bound > F("1/2"),
        },
    )


def kalman():
    p, r = s.symbols("p r", positive=True)
    k = s.symbols("k", real=True)
    objective = (1 - k) ** 2 * p + k**2 * r
    best = p / (p + r)
    identity = require_zero(objective - p * r / (p + r) - (p + r) * (k - best) ** 2)
    cases = 0
    for pv, rv, kv in product(
        map(F, ["1/4", "1/2", "1", "2", "4"]),
        map(F, ["1/4", "1/2", "1", "2", "4"]),
        [F(i, 4) for i in range(-4, 9)],
    ):
        value = (1 - kv) ** 2 * pv + kv**2 * rv
        assert value - pv * rv / (pv + rv) == (pv + rv) * (kv - pv / (pv + rv)) ** 2
        cases += 1
    # Nonzero correlation violates the independent-error objective.
    c = F("1/2")

    def correlated(gain):
        return (1 - gain) ** 2 + 4 * gain**2 + 2 * gain * (1 - gain) * c

    assert correlated(F("1/8")) < correlated(F("1/5"))
    return record(
        "kalman",
        "The gain balances two errors",
        ["ctrl-kalman"],
        "Can completion of squares expose the optimal gain and its assumptions?",
        "Scalar error variance with positive variances and zero cross-covariance; no stochastic calibration or multivariate claim.",
        "Estimate cross-covariance on held-out sensor traces before using the independent-error gain.",
        "Reject the independent-error model if residual correlation invalidates its objective.",
        evidence="CAS identity + exact rational sweep",
        cases=cases,
        checks=[identity],
        conclusion="Every tested gain has exactly the predicted nonnegative excess variance; a correlated fixture changes the optimum.",
        formula=str(s.factor(objective)),
        optimal_gain=str(best),
        latex=s.latex(best),
        example={
            "p": "1",
            "r": "4",
            "gain": "1/5",
            "variance": "4/5",
            "wrong_gain": "1/2",
            "wrong_variance": "5/4",
        },
        negative_control={
            "cross_covariance": str(c),
            "independent_gain": "1/5",
            "correlated_gain": "1/8",
            "variance_independent_gain": str(correlated(F("1/5"))),
            "variance_correlated_gain": str(correlated(F("1/8"))),
        },
    )


def saturation():
    rows, first = [], None
    for bound in range(1, 5):

        def clip(x, limit=bound):
            return min(limit, max(-limit, x))

        failures = []
        for a, b, c in product(range(-bound, bound + 1), repeat=3):
            left, right = clip(clip(a + b) + c), clip(a + clip(b + c))
            if left != right:
                failures.append(
                    {"bound": bound, "a": a, "b": b, "c": c, "left": left, "right": right}
                )
        assert failures
        if first is None:
            first = failures[0]
        assert all(clip(clip(x)) == clip(x) for x in range(-12, 13))
        rows.append(
            {"bound": bound, "triples": (2 * bound + 1) ** 3, "nonassociative": len(failures)}
        )
    return record(
        "saturation",
        "Saturation breaks an innocent rewrite",
        ["tao-equations"],
        "May a command-combining pipeline regroup saturated additions?",
        "Exhaustive finite integer tables for four clipping bounds; not a classification of real-valued controllers or a new algebraic theorem.",
        "Check actual command-combining operators and compiler rewrites against frozen finite countermodels.",
        "Reject any reassociation rule when one input triple changes the applied command.",
        evidence="Finite exhaustive countermodels",
        cases=sum(r["triples"] for r in rows),
        rows=rows,
        witness=first,
        conclusion="Clipping is idempotent on the tested inputs, but saturated addition is not associative.",
    )


def sumsets():
    rows = []
    domain = list(range(-3, 4))
    for mask in range(1, 1 << len(domain)):
        A = [x for i, x in enumerate(domain) if mask & (1 << i)]
        AA = {x + y for x in A for y in A}
        AAA = {x + y for x in AA for y in A}
        hull = max(AAA) - min(AAA) + 1
        rows.append(
            {
                "A": A,
                "doubling": str(F(len(AA), len(A))),
                "reachable_three": sorted(AAA),
                "hull_points": hull,
                "unreachable_hull_points": hull - len(AAA),
            }
        )
    witness = next(row for row in rows if row["A"] == [-3, 3])
    assert witness["hull_points"] == 19 and len(witness["reachable_three"]) == 4
    return record(
        "sumsets",
        "A reachable interval can hide holes",
        ["tao-sumsets"],
        "When does a compact reachable-set description erase useful structure?",
        "All 127 nonempty subsets of seven integers, three independent additive steps. No PFR theorem transfer or general compression benefit.",
        "Compare exact unions and interval hulls on quantized actuator models with measured checking cost.",
        "Abandon compression if it excludes any reachable state or its membership cost exceeds the exact representation.",
        evidence="Finite exhaustive set arithmetic",
        cases=len(rows),
        rows=rows,
        witness=witness,
        conclusion="With increments {-3, 3}, three steps reach four points; the integer interval hull contains nineteen.",
    )


def entropy():
    rows = []
    for k in range(1, 17):
        probability = F(1, 2**k)
        p = float(probability)
        rows.append(
            {
                "k": k,
                "tail_probability": str(probability),
                "mean_square": str(100 * probability),
                "entropy_bits_approx": -p * math.log2(p) - (1 - p) * math.log2(1 - p),
                "max_error": 10,
            }
        )
    assert all(row["max_error"] > 1 for row in rows)
    assert rows[-1]["entropy_bits_approx"] < rows[0]["entropy_bits_approx"]
    return record(
        "entropy",
        "Low entropy does not remove a rare failure",
        ["tao-sumsets"],
        "Can uncertainty or average error replace a hard support bound?",
        "Constructed two-point distributions. Probabilities and moments are exact; displayed logarithms use floating point. This is our falsifier, not a result attributed to Tao.",
        "Compare mean, quantile and support contracts on the same held-out perception errors.",
        "Reject any hard-safety implication based only on decreasing entropy or mean-square error.",
        evidence="Exact discrete distribution + approximate entropy",
        cases=len(rows),
        rows=rows,
        conclusion="Entropy and mean-square error decrease while the worst possible error stays at 10.",
    )


def tropical_feasible(point):
    x, y, z = point
    return z <= max(x, y) and max(y + 1, z - 2) <= x


def tropical():
    rows = []
    for shift in range(17):
        output, better = (shift + 1, shift, shift), (shift, shift - 1, shift)
        assert tropical_feasible(output) and tropical_feasible(better)
        assert output[0] - better[0] == 1
        rows.append({"anchor": shift, "output": output, "better": better, "cost_gap": 1})
    finite = [(x, y, 0) for x, y in product(range(-6, 7), repeat=2) if tropical_feasible((x, y, 0))]
    assert min(p[0] for p in finite) == 0
    assert not tropical_feasible((-1, -1, 0))
    return record(
        "tropical",
        "Feasible does not mean optimal",
        ["oai-tropical"],
        "Can a checker keep feasibility separate from objective quality?",
        "Exact arithmetic on the upstream displayed witness and 17 common translations. No execution replay of the elimination algorithm; grid optimality is finite only.",
        "Require separate feasibility and bound certificates from one real allocation consumer.",
        "Reject an optimality claim when a feasible point with smaller cost is supplied, even if the solver terminated.",
        evidence="Pinned-source witness recomputation",
        cases=17 + 169,
        rows=rows,
        conclusion="Both displayed points are feasible, but their costs are 1 and 0. The strict gap survives every tested common translation.",
        constraints=["max(x, y) >= z", "x >= max(y + 1, z - 2)"],
        objective="minimize x",
        finite_grid_minimum=0,
        negative_control={"point": [-1, -1, 0], "feasible": False},
    )


def valid_schedule(n, edges, slots, machines=3):
    """Small independent certificate checker, with zero-based unit-duration slots."""
    if len(slots) != n or any(type(t) is not int or t < 0 for t in slots):
        return False
    if any(slots.count(t) > machines for t in set(slots)):
        return False
    return all(0 <= u < n and 0 <= v < n and slots[u] < slots[v] for u, v in edges)


def optimal_schedule(n, edges, machines=3):
    if not 1 <= n <= 10 or not 1 <= machines <= 3:
        raise ValueError("bounded experiment: 1..10 jobs and 1..3 machines")
    predecessors = [0] * n
    for u, v in edges:
        if not 0 <= u < n or not 0 <= v < n:
            raise ValueError("invalid vertex")
        predecessors[v] |= 1 << u
    queue = deque([(0, [])])
    seen = {0}
    while queue:
        done, batches = queue.popleft()
        if done == (1 << n) - 1:
            slots = [0] * n
            for time, batch in enumerate(batches):
                for job in batch:
                    slots[job] = time
            assert valid_schedule(n, edges, slots, machines)
            return slots
        ready = [
            i for i in range(n) if not done & (1 << i) and predecessors[i] & done == predecessors[i]
        ]
        for count in range(1, min(machines, len(ready)) + 1):
            for batch in combinations(ready, count):
                reached = done | sum(1 << i for i in batch)
                if reached not in seen:
                    seen.add(reached)
                    queue.append((reached, batches + [batch]))
    raise ValueError("cyclic precedence has no feasible schedule")


def scheduling():
    possible = list(combinations(range(5), 2))
    gaps, examples = 0, []
    for mask in range(1 << len(possible)):
        edges = [edge for i, edge in enumerate(possible) if mask & (1 << i)]
        slots = optimal_schedule(5, edges)
        longest = [1] * 5
        for v in range(5):
            longest[v] = 1 + max([longest[u] for u, w in edges if w == v], default=0)
        lower = max(2, max(longest))
        optimum = max(slots) + 1
        assert lower <= optimum
        gaps += lower < optimum
        if lower < optimum and len(examples) < 5:
            examples.append(
                {"edges": edges, "lower_bound": lower, "optimum": optimum, "slots": slots}
            )
    edges = [(a, b) for a in range(4) for b in range(4, 8)]
    slots = optimal_schedule(8, edges)
    assert max(slots) + 1 == 4
    assert not valid_schedule(4, [], [0, 0, 0, 0])
    assert not valid_schedule(2, [(0, 1)], [0, 0])
    return record(
        "scheduling",
        "A lower bound is not a schedule",
        ["oai-scheduling", "oai-tropical"],
        "When do workload and critical-path bounds miss the optimum?",
        "All 1,024 forward-edge DAGs on five labeled unit jobs, plus one eight-job fixture, on three identical machines. Offline, no release times, WCET, transport, or RTOS model.",
        "Add release times and bounded transport costs, then compare independently checked schedules against the exact small-instance oracle.",
        "Reject a quality claim unless feasibility is checked and its attained makespan matches a sound bound.",
        evidence="Exhaustive finite search + separate feasibility checker",
        cases=1025,
        conclusion=f"The elementary bound is loose on {gaps} of 1,024 five-job DAGs. The layered eight-job fixture has lower bound 3 and optimum 4.",
        loose_bound_cases=gaps,
        examples=examples,
        witness={
            "n": 8,
            "edges": edges,
            "slots": slots,
            "lower_bound": 3,
            "optimum": 4,
            "stronger_bound": "Four jobs in each of two nonoverlapping layers require at least two slots per layer.",
        },
    )


def build_report():
    experiments = [
        fn()
        for fn in (lyapunov, braking, kalman, saturation, sumsets, entropy, tropical, scheduling)
    ]
    payload = {
        "schema_version": 1,
        "campaign": "Math explainers 144",
        "as_of": "2026-10-28",
        "engine": {"sympy": s.__version__},
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Eight completed finite/CAS experiments, not new theorems, upstream proof replay, performance benchmarks or physical safety validation.",
        "sources": SOURCES,
        "experiments": experiments,
    }
    payload["sha256"] = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return payload


if __name__ == "__main__":
    report = build_report()
    DEST.parent.mkdir(parents=True, exist_ok=True)
    DEST.write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                "experiments": len(report["experiments"]),
                "cases": sum(e["cases"] for e in report["experiments"]),
                "sha256": report["sha256"],
                "output": str(DEST),
            },
            indent=2,
        )
    )
