#!/usr/bin/env python3
"""Independent review of saved comparison data; standard library only.

This script does not import comparison.py or its numerical solver. It checks
all exact parameters, then integrates the derived error ODE with fixed-step
RK4 for six saved traces. It is numerical consistency evidence, not a proof
of a continuous-time enclosure or of the physical model.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import platform

ROOT = Path(__file__).resolve().parent
PROFILES = {
    "short_high_jerk": (F(10), F(1, 50)),
    "long_high_jerk": (F(10), F(1, 4)),
    "slow_precision": (F(1, 20), F(1, 2)),
}
METHODS = ("zero_jerk_ff", "nominal_rate", "reciprocal_midpoint")
RATES = ("fixed_8", "fixed_10", "fixed_12", "aligned_smooth_stress")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_parameters(report):
    expected = set(product(PROFILES, (1, 10), RATES, (0.0, 0.0005), METHODS))
    seen = set()
    for row in report["rows"]:
        key = (row["profile"], row["sigma"], row["rate_signal"],
               row["disturbance_bound_m_s2"], row["method"])
        assert key in expected and key not in seen
        seen.add(key)
        s = F(row["sigma"])
        w = F(str(row["disturbance_bound_m_s2"]))
        j, h = PROFILES[row["profile"]]
        assert F(str(row["reference_jerk_bound_m_s3"])) == j
        assert F(str(row["reference_segment_duration_s"])) == h
        k = {"zero_jerk_ff": F(0), "nominal_rate": 1/(10*s),
             "reciprocal_midpoint": 5/(48*s)}[row["method"]]
        assert k == F(row["kappa_s_exact"])
        delta = max(abs(k-1/(8*s)), abs(k-1/(12*s)))
        radius = (w+delta*j)/(2*s*s)
        assert delta == F(row["residual_delta_s_exact"])
        assert radius == F(row["sufficient_radius_m_exact"])
        authority = j*h+24*s*s*radius+abs(k)*j+w
        assert abs(float(authority)-row["sufficient_effective_target_bound_m_s2"]) < 1e-12
        assert abs(float(2*j*h**3)-row["reference_final_position_m"]) < 1e-12
        # Algebraic scaled counterpart of the base actual-jerk bound.
        jerk_bound = 12*s*(56*s*s*radius+abs(k)*j+w)
        assert row["measured_peak_actual_jerk_m_s3"] <= float(jerk_bound)+1e-8
    assert seen == expected
    return len(seen)


def independently_integrate(report):
    checks = []
    for profile in ("short_high_jerk", "long_high_jerk"):
        _, h_fraction = PROFILES[profile]
        h = float(h_fraction)
        for method, kappa in (("zero_jerk_ff", 0.0), ("nominal_rate", 0.1),
                              ("reciprocal_midpoint", 5/48)):
            expected = report["figure_trace_data"][f"{profile}|1|fixed_12|0|{method}"]
            state = [0.0, 0.0, 0.0]
            values, times = [], []
            for segment, jerk in enumerate((10.0, -10.0, -10.0, 10.0, 0.0)):
                duration = h if segment < 4 else 4.0
                intervals = 250 if segment < 4 else 1000
                dt = duration/intervals
                subdivisions = max(1, math.ceil(dt/0.0005))
                step = dt/subdivisions
                start = segment*h
                values.append(state[0])
                times.append(start)

                # Independent coordinates: error ODE, not the original
                # physical-state ODE used by comparison.py.
                def rhs(z):
                    x, v, a = z
                    return [v, a, 12*(-8*x-6*v-1.5*a+kappa*jerk)-jerk]

                for sample in range(intervals):
                    for _ in range(subdivisions):
                        a = rhs(state)
                        b = rhs([x+step*y/2 for x, y in zip(state, a)])
                        c = rhs([x+step*y/2 for x, y in zip(state, b)])
                        d = rhs([x+step*y for x, y in zip(state, c)])
                        state = [x+step*(aa+2*bb+2*cc+dd)/6
                                 for x, aa, bb, cc, dd in zip(state, a, b, c, d)]
                    values.append(state[0])
                    times.append(start+(sample+1)*dt)
            assert len(values) == len(expected)
            assert max(abs(t-point[0]) for t, point in zip(times, expected)) < 1e-12
            error = max(abs(x-point[1]) for x, point in zip(values, expected))
            assert error < 1e-9, (profile, method, error)
            checks.append({"profile": profile, "method": method,
                           "max_position_difference_m": error,
                           "sample_count": len(values)})
    return checks


def main():
    data_path = ROOT/"comparison-results.json"
    report = json.loads(data_path.read_text())
    assert report["source_sha256"] == sha(ROOT/"comparison.py")
    row_count = check_parameters(report)
    traces = independently_integrate(report)
    table = {}
    for profile, sigma in (("short_high_jerk", 1), ("long_high_jerk", 10)):
        table[f"{profile}|sigma={sigma}"] = {
            method: max(row["measured_peak_abs_position_error_m"]*1000
                        for row in report["rows"]
                        if row["profile"] == profile and row["sigma"] == sigma
                        and row["method"] == method
                        and row["disturbance_bound_m_s2"] == .0005)
            for method in METHODS}
    out = {
        "passed": True,
        "scope": "Independent exact parameter checks plus six numerical error-ODE traces. No validated numerical enclosure or hardware evidence.",
        "python": platform.python_version(),
        "review_source_sha256": sha(Path(__file__)),
        "comparison_source_sha256": sha(ROOT/"comparison.py"),
        "comparison_results_sha256": sha(data_path),
        "exact_parameter_cases_checked": row_count,
        "independent_solver": "Standard-library classical RK4 on the error ODE, fixed r=12/s, sigma=1, w=0; maximum step 0.0005 s, split at every jerk boundary.",
        "trace_checks": traces,
        "table_peak_error_mm": table,
    }
    (ROOT/"review-numeric.json").write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps({"passed": True, "exact_parameter_cases": row_count,
                      "independent_traces": len(traces),
                      "maximum_trace_difference_m": max(t["max_position_difference_m"] for t in traces)}))


if __name__ == "__main__":
    main()
