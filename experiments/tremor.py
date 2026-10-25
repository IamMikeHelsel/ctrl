# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.5.4", "numba==0.68.0", "ruckig==0.19.4", "OneEuroFilter==0.2.1"]
# ///
"""AI-assisted, reproducible timing diagnostics; simulation only, no hardware API.

Run: uv run experiments/tremor.py --output work/vision/tremor-results.json
The clocks, timestamps, states, noise and gains are explicit. No novelty is assumed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path


def clip_polygon(poly, a, b, c):
    """Intersect a convex (clock-rate, offset) polygon with a*x+b*y <= c."""
    out = []
    if not poly:
        return out
    for p, q in zip(poly, poly[1:] + poly[:1], strict=True):
        fp, fq = a * p[0] + b * p[1] - c, a * q[0] + b * q[1] - c
        if fp <= 1e-14:
            out.append(p)
        if (fp <= 0) != (fq <= 0):
            w = fp / (fp - fq)
            out.append((p[0] + w * (q[0] - p[0]), p[1] + w * (q[1] - p[1])))
    return out


def clock_update(poly, device, receipt, delay_max=0.020):
    poly = clip_polygon(poly, device, 1, receipt)
    return clip_polygon(poly, -device, -1, delay_max - receipt)


def clock_probe():
    import numpy as np

    a, b = 1 / 1.0001, -0.005 / 1.0001
    rows = []
    for seed in range(10):
        rng = np.random.default_rng(seed)
        poly = [(0.9998, -0.05), (1.0002, -0.05), (1.0002, 0.05), (0.9998, 0.05)]
        widths, errors, violations = [], [], 0
        calibration, fixed_errors = [], []
        fixed_offset = 0.0
        for t in np.arange(0, 10, 1 / 60):
            device = (t - b) / a
            receipt = t + rng.uniform(0, 0.020)
            poly = clock_update(poly, float(device), float(receipt))
            assert poly, "Valid affine clock became infeasible"
            vals = [aa * device + bb for aa, bb in poly]
            lo, hi = min(vals), max(vals)
            violations += int(t < lo - 1e-10 or t > hi + 1e-10)
            widths.append(hi - lo)
            errors.append(receipt - t)
            if len(calibration) < 60:
                calibration.append(receipt - device - 0.010)
                fixed_offset = float(np.mean(calibration))
            else:
                fixed_errors.append(device + fixed_offset - t)
        rows.append(
            {
                "seed": seed,
                "containment_violations": violations,
                "fixed_offset_calibrated_rmse_ms": 1000
                * float(np.sqrt(np.mean(np.square(fixed_errors)))),
                "final_width_ms": 1000 * widths[-1],
                "mean_width_ms": 1000 * float(np.mean(widths)),
                "arrival_error_rms_ms": 1000 * float(np.sqrt(np.mean(np.square(errors)))),
            }
        )
    # Identical device/receipt pairs: one admissible world, one violates the delay envelope.
    # World A t=c, delay=.01; world B t=c-.03, delay=.04. Receiver cannot distinguish.
    pa = [(0.9998, -0.05), (1.0002, -0.05), (1.0002, 0.05), (0.9998, 0.05)]
    for c in np.arange(0, 2, 1 / 60):
        pa = clock_update(pa, float(c), float(c + 0.01))
    hidden_excluded = bool(pa) and min(aa * 1 + bb for aa, bb in pa) > 0.97
    assert hidden_excluded
    return {
        "runs": rows,
        "hidden_delay_violation_detected": False,
        "hidden_delay_world_excluded_but_model_still_feasible": hidden_excluded,
        "claim": "Conditional containment only; standard affine-clock feasibility, not new.",
        "floating_tolerance_s": 1e-10,
    }


def target(t, reversal=False):
    if reversal:
        # Smooth tanh transition followed by its reverse; not a contact impact.
        x, y = (t - 3) / 0.4, (t - 6) / 0.4
        q = 0.08 * (math.tanh(x) - math.tanh(y))
        v = 0.2 * (1 - math.tanh(x) ** 2 - (1 - math.tanh(y) ** 2))
        return q, v
    return 0.1 * math.sin(math.pi * t), 0.1 * math.pi * math.cos(math.pi * t)


def phase_metrics(times, values, reference="position"):
    import numpy as np

    design = np.column_stack(
        (np.sin(math.pi * times), np.cos(math.pi * times), np.ones(len(times)))
    )
    coef = np.linalg.lstsq(design, values, rcond=None)[0]
    phase = math.atan2(coef[1], coef[0])
    expected = 0 if reference == "position" else math.pi / 2
    lag = math.atan2(math.sin(expected - phase), math.cos(expected - phase)) / math.pi
    return {"phase_lag_ms": 1000 * lag, "fundamental_amplitude": float(math.hypot(*coef[:2]))}


def estimator_probe():
    import numpy as np
    from OneEuroFilter import OneEuroFilter

    runs = []
    diagnostic = []
    for seed in range(10):
        rng = np.random.default_rng(seed)
        times = np.cumsum(rng.uniform(0.8, 1.2, 610) / 60)
        times = np.r_[0.0, times[times < 10]]
        dt = np.diff(times)
        constant = 0.2 * times
        nominal = np.diff(constant) * 60
        actual = np.diff(constant) / dt
        diagnostic.append(
            {
                "seed": seed,
                "nominal_velocity_rms_error": float(np.sqrt(np.mean((nominal - 0.2) ** 2))),
                "actual_velocity_max_error": float(np.max(abs(actual - 0.2))),
            }
        )
        assert np.max(abs(actual - 0.2)) < 1e-12
        q = 0.1 * np.sin(math.pi * times) + rng.normal(0, 0.0005, len(times))
        true_v = 0.1 * math.pi * np.cos(math.pi * times)
        methods = {
            "nominal_difference": np.r_[0, np.diff(q) * 60],
            "actual_difference": np.r_[0, np.diff(q) / dt],
        }
        for hz in (2, 4, 8, 16):
            f = OneEuroFilter(freq=60, mincutoff=hz, beta=0.1, dcutoff=1.0)
            filtered = np.array([f(float(x), float(t)) for x, t in zip(q, times, strict=True)])
            methods[f"one_euro_{hz}Hz_then_actual_difference"] = np.r_[0, np.diff(filtered) / dt]
        for window in (3, 5, 9):
            vel = np.zeros(len(q))
            for i in range(2, len(q)):
                lo = max(0, i - window + 1)
                tt = times[lo : i + 1] - times[i]
                design = np.column_stack((np.ones(len(tt)), tt, 0.5 * tt**2))
                vel[i] = np.linalg.lstsq(design, q[lo : i + 1], rcond=None)[0][1]
            methods[f"causal_quadratic_{window}"] = vel
        for process in (0.01, 0.1, 1.0, 10.0):
            x, cov = np.array([q[0], 0.0]), np.diag([1.0, 1.0])
            vel = [0.0]
            for i, h in enumerate(dt, 1):
                trans = np.array([[1.0, h], [0.0, 1.0]])
                noise = process * np.array([[h**3 / 3, h * h / 2], [h * h / 2, h]])
                x, cov = trans @ x, trans @ cov @ trans.T + noise
                gain = cov[:, 0] / (cov[0, 0] + 0.0005**2)
                x += gain * (q[i] - x[0])
                cov -= np.outer(gain, cov[0, :])
                vel.append(float(x[1]))
            methods[f"kalman_accel_psd_{process}"] = np.array(vel)
        mask = times >= 2
        for name, v in methods.items():
            runs.append(
                {
                    "seed": seed,
                    "method": name,
                    "velocity_rmse": float(np.sqrt(np.mean((v[mask] - true_v[mask]) ** 2))),
                    **phase_metrics(times[mask], v[mask], "velocity"),
                }
            )
    return {
        "constant_velocity": diagnostic,
        "noisy_sine_frontier": runs,
        "short_interval_counterexample": {
            "interval_s": 1e-6,
            "position_noise_jump_rad": 0.001,
            "actual_dt_velocity_error_rad_s": 1000.0,
        },
        "claim": "Classic timing and filtering baselines; no proposed superior estimator.",
    }


def make_trace(seed, case, duration=10.0):
    import numpy as np

    rng = np.random.default_rng(seed)
    camera_jitter = case in ("camera_jitter", "camera_jitter_noise", "queue_loss", "blackout")
    noise_rng = np.random.default_rng(10000 + seed)
    t, seq, records = 0.0, 0, []
    while t < duration:
        delay = 0.0
        if case in ("queue_loss", "blackout"):
            delay = 0.002 if int(t / 0.25) % 2 == 0 else 0.020
            if seq % 20 == 19:
                t += rng.uniform(0.8, 1.2) / 60
                seq += 1
                continue
            if seq % 20 == 18:
                delay += 0.040
        noise = (
            0
            if case
            in ("clean", "camera_jitter", "servo_jitter", "friction", "saturation", "resonance")
            else noise_rng.normal(0, 0.0005)
        )
        if not (case == "blackout" and 4 <= t < 4.1):
            records.append((t, t + delay, seq, target(t)[0] + noise))
        t += (rng.uniform(0.8, 1.2) if camera_jitter else 1.0) / 60
        seq += 1
    servo_ticks = [0]
    end_tick = round(duration / 0.00005)
    while servo_ticks[-1] < end_tick:
        ticks = int(rng.integers(16, 25)) if case in ("servo_jitter", "servo_jitter_noise") else 20
        servo_ticks.append(min(end_tick, servo_ticks[-1] + ticks))
    return np.array(sorted(records, key=lambda x: x[1])), np.array(servo_ticks) * 0.00005


def references(records, times, method):
    import numpy as np
    import ruckig

    pos, vel = [], []
    last_seq, idx, rejected, expired, failures = -1, 0, 0, 0, 0
    hist, plan, plan_start = [], None, 0.0
    current = (0.0, 0.0, 0.0)
    was_expired = False
    planner = ruckig.Ruckig(1)
    jerk = float(method.split("j")[-1]) if "_j" in method else 0.0
    for t in times:
        changed = False
        while idx < len(records) and records[idx, 1] <= t + 1e-12:
            capture, _, seq, q = records[idx]
            idx += 1
            if seq <= last_seq or (hist and capture <= hist[-1][0]):
                rejected += 1
                continue
            last_seq = seq
            hist.append((capture, q))
            hist = hist[-5:]
            changed = True
        if method == "oracle":
            qp, vp = target(t)
            pos.append(qp)
            vel.append(vp)
            continue
        if not hist:
            pos.append(current[0])
            vel.append(current[1])
            continue
        capture, q = hist[-1]
        age = t - capture
        v_actual = v_nominal = 0.0
        if len(hist) >= 2:
            v_actual = (q - hist[-2][1]) / (capture - hist[-2][0])
            v_nominal = (q - hist[-2][1]) * 60
        if method == "hold":
            current = (q, 0.0, 0.0)
        elif method in ("extrap_actual", "extrap_nominal"):
            v = v_actual if method == "extrap_actual" else v_nominal
            current = (q + v * age, v, 0.0)
        else:
            if plan is not None:
                pp, vv, aa = plan.at_time(float(t - plan_start))
                current = (pp[0], vv[0], aa[0])
            is_expired = method.startswith("fresh") and age > 0.060
            expire_edge = is_expired and not was_expired
            expired += int(expire_edge)
            if changed or expire_edge:
                # Same causal estimator and age compensation for both Ruckig variants.
                v = max(-0.8, min(0.8, v_actual))
                inp = ruckig.InputParameter(1)
                inp.current_position, inp.current_velocity, inp.current_acceleration = (
                    [current[0]],
                    [current[1]],
                    [current[2]],
                )
                if is_expired:
                    # Explicit finite stop target, not a claim that holding is safe in every plant.
                    stopping = current[1] * abs(current[1]) / 6 + current[1] * 3 / (2 * jerk)
                    inp.target_position, inp.target_velocity = [current[0] + stopping], [0.0]
                else:
                    inp.target_position, inp.target_velocity = [q + v * age], [v]
                inp.target_acceleration = [0.0]
                inp.max_velocity, inp.max_acceleration, inp.max_jerk = [1.0], [3.0], [jerk]
                new_plan = ruckig.Trajectory(1)
                try:
                    result = planner.calculate(inp, new_plan)
                    if int(result) < 0:
                        raise RuntimeError(str(result))
                    plan, plan_start = new_plan, t
                except (RuntimeError, ruckig.RuckigError):
                    failures += 1
            was_expired = is_expired
        pos.append(current[0])
        vel.append(current[1])
    return (
        np.array(pos),
        np.array(vel),
        {
            "reordered_rejected": rejected,
            "expiration_events": expired,
            "planner_failures": failures,
        },
    )


def plant_runner():
    """JIT is numerical simulation only, never used as proof evidence."""
    import numpy as np
    from numba import njit

    @njit
    def rhs(y, u, friction, resonance):
        q, v, tau, load_q, load_v = y
        force = friction * math.tanh(v / 0.002)
        coupling = 0.0
        if resonance:
            coupling = 1600 * (q - load_q) + 1.5 * (v - load_v)
        return np.array(
            [
                v,
                tau - 2 * v - force - coupling,
                (u - tau) / 0.002,
                load_v if resonance else 0.0,
                coupling / 0.25 if resonance else 0.0,
            ]
        )

    @njit
    def run(
        times, rp, rv, friction, limit, resonance, max_step, feedback_mode=0, measured_noise=None
    ):
        y = np.array([0.0, 0.0, 0.0, 0.0, 0.0])
        qs = np.zeros(len(times))
        sums = np.zeros(6)
        peak_jerk, max_error, saturated = 0.0, 0.0, 0.0
        previous_measured_q, filtered_velocity = 0.0, 0.0
        for i in range(len(times) - 1):
            measured_q = y[0] + (measured_noise[i] if measured_noise is not None else 0.0)
            measured_v = y[1]
            if feedback_mode > 0:
                measured_v = 0.0
                if i > 0:
                    actual_dt = times[i] - times[i - 1]
                    divisor = 0.001 if feedback_mode == 1 else actual_dt
                    measured_v = (measured_q - previous_measured_q) / divisor
                    if feedback_mode == 3:
                        alpha = actual_dt / (actual_dt + 1 / (2 * math.pi * 100))
                        filtered_velocity += alpha * (measured_v - filtered_velocity)
                        measured_v = filtered_velocity
            previous_measured_q = measured_q
            cmd = 100 * (rp[i] - measured_q) + 18 * (rv[i] - measured_v)
            u = max(-limit, min(limit, cmd))
            interval = times[i + 1] - times[i]
            steps = max(1, int(math.ceil(interval / max_step - 1e-8)))
            h = interval / steps
            for j in range(steps):
                t = times[i] + j * h
                k1 = rhs(y, u, friction, resonance)
                mid = y + h * k1 / 2
                k2 = rhs(mid, u, friction, resonance)
                k3 = rhs(y + h * k2 / 2, u, friction, resonance)
                k4 = rhs(y + h * k3, u, friction, resonance)
                if t >= 2:
                    tq = 0.1 * math.sin(math.pi * (t + h / 2))
                    error = mid[0] - tq
                    # Jerk follows the ODE, including actuator and smooth friction derivatives.
                    fric_derivative = friction / 0.002 * (1 - math.tanh(mid[1] / 0.002) ** 2)
                    coupling_derivative = 0.0
                    if resonance:
                        coupling_derivative = 1600 * (mid[1] - mid[4]) + 1.5 * (k2[1] - k2[4])
                    jerk = k2[2] - (2 + fric_derivative) * k2[1] - coupling_derivative
                    sums[0] += jerk * jerk * h
                    sums[1] += error * error * h
                    sums[2] += mid[2] * mid[2] * h
                    sums[3] += h
                    peak_jerk = max(peak_jerk, abs(jerk))
                    max_error = max(max_error, abs(error))
                    saturated += h if abs(cmd) > limit else 0.0
                y = y + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
            qs[i + 1] = y[0]
        return qs, np.array(
            [
                math.sqrt(sums[0] / sums[3]),
                peak_jerk,
                math.sqrt(sums[1] / sums[3]),
                max_error,
                math.sqrt(sums[2] / sums[3]),
                saturated,
            ]
        )

    return run


def robot_probe(outdir, seeds=10, cases=None):
    import numpy as np

    cases = cases or [
        "clean",
        "noise_only",
        "camera_jitter",
        "camera_jitter_noise",
        "servo_jitter",
        "servo_jitter_noise",
        "queue_loss",
        "blackout",
        "friction",
        "saturation",
        "resonance",
    ]
    methods = ["oracle", "hold", "extrap_nominal", "extrap_actual"] + [
        f"{name}_j{j}" for name in ("ruckig", "fresh") for j in (30, 100, 300)
    ]
    run = plant_runner()
    rows, convergence = [], []
    freshness_checks = []
    for case in cases:
        case_seeds = 1 if case in ("clean", "friction", "saturation", "resonance") else seeds
        for seed in range(case_seeds):
            records, times = make_trace(seed, case)
            tracepath = outdir / f"trace-{case}-{seed}.npz"
            np.savez_compressed(
                tracepath,
                columns=np.array(["capture", "receipt", "seq", "q"]),
                observations=records,
                actuation_times=times,
            )
            paired_refs = {}
            for method in methods:
                rp, rv, events = references(records, times, method)
                if method.startswith("ruckig"):
                    paired_refs[method] = (rp, rv)
                if method.startswith("fresh") and events["expiration_events"] == 0:
                    pp, vv = paired_refs[method.replace("fresh", "ruckig")]
                    equal = bool(np.array_equal(rp, pp) and np.array_equal(rv, vv))
                    assert equal, "Freshness adapter altered a nonexpired trajectory"
                    freshness_checks.append(
                        {"case": case, "seed": seed, "method": method, "equal": equal}
                    )
                params = (
                    3.0 if case == "friction" else 0.0,
                    2.0 if case == "saturation" else 20.0,
                    case == "resonance",
                )
                qs, metrics = run(times, rp, rv, *params, 0.00005)
                mask = times >= 2
                row = {
                    "case": case,
                    "seed": seed,
                    "method": method,
                    **events,
                    **dict(
                        zip(
                            [
                                "jerk_rms",
                                "jerk_peak",
                                "tracking_rms",
                                "tracking_peak",
                                "torque_rms",
                                "saturation_seconds",
                            ],
                            metrics.tolist(),
                            strict=True,
                        )
                    ),
                    **phase_metrics(times[mask], qs[mask]),
                }
                rows.append(row)
                if (
                    seed == 0
                    and case in ("queue_loss", "friction", "resonance")
                    and method in ("hold", "fresh_j100")
                ):
                    q2, m2 = run(times, rp, rv, *params, 0.000025)
                    relative = abs(m2[:5] - metrics[:5]) / np.maximum(abs(m2[:5]), 1e-10)
                    convergence.append(
                        {
                            "case": case,
                            "method": method,
                            "max_relative_metric_change": float(max(relative)),
                            "passes_one_percent": bool(max(relative) < 0.01),
                        }
                    )
                    np.savez_compressed(
                        outdir / f"trajectory-{case}-{method}.npz",
                        times=times,
                        q=qs,
                        q_half_step=q2,
                        rp=rp,
                        rv=rv,
                    )
            print(json.dumps({"completed_case": case, "seed": seed}), flush=True)
    return {
        "runs": rows,
        "convergence": convergence,
        "nonexpired_freshness_checks": freshness_checks,
        "deterministic_cases": ["clean", "friction", "saturation", "resonance"],
        "jerk_joint": "motor; flexible-load jerk not reported",
        "limitations": [
            "Synthetic one-joint model, no claim about prevalence in robots.",
            "V3 assumes already calibrated acquisition timestamps; V1 is not integrated.",
            "Ruckig Community offline replanning, not paid Pro predictive tracking.",
            "Reversal, reset, and full factorial crosses remain separate follow-up tests.",
            "No passivity or safety certification; no measured wall-clock deadline guarantee.",
        ],
    }


def convergence_status(checks):
    """No executed numerical check is not evidence of convergence."""
    return all(x["passes_one_percent"] for x in checks) if checks else None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("work/vision/tremor-results.json"))
    parser.add_argument("--seeds", type=int, default=10)
    parser.add_argument("--cases", default="")
    args = parser.parse_args()
    if args.seeds < 1:
        parser.error("seeds must be positive")
    outdir = args.output.parent / (args.output.stem + "-traces")
    outdir.mkdir(parents=True, exist_ok=True)
    args.output.with_name(args.output.stem + "-source.py").write_bytes(Path(__file__).read_bytes())
    result = {
        "status": "running",
        "ai_assisted": True,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "units": "seconds,radians,Newton-metres",
        "clock": clock_probe(),
        "estimator": estimator_probe(),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    result["robot"] = robot_probe(outdir, args.seeds, args.cases.split(",") if args.cases else None)
    result["status"] = "complete"
    result["all_convergence_checks_pass"] = convergence_status(result["robot"]["convergence"])
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                "output": str(args.output),
                "runs": len(result["robot"]["runs"]),
                "convergence": result["all_convergence_checks_pass"],
            }
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
