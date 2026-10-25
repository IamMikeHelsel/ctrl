# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.5.4", "numba==0.68.0", "ruckig==0.19.4", "OneEuroFilter==0.2.1"]
# ///
"""Direct1kHz feedback differentiation experiment; AI-assisted, simulation only."""

import hashlib
import json
from pathlib import Path

import numpy as np
from tremor import make_trace, phase_metrics, plant_runner, references


def main():
    root = Path("work/vision")
    trace_dir = root / "feedback-traces"
    trace_dir.mkdir(exist_ok=True)
    paths = [Path(__file__), Path(__file__).with_name("tremor.py")]
    hashes = {}
    for source in paths:
        saved = root / ("feedback-source-" + source.name)
        saved.write_bytes(source.read_bytes())
        hashes[str(saved)] = hashlib.sha256(saved.read_bytes()).hexdigest()
    run = plant_runner()
    rows, convergence = [], []
    for case in ("clean", "jitter", "noise", "jitter_noise"):
        for seed in range(1 if case == "clean" else 10):
            records, times = make_trace(seed, "servo_jitter" if "jitter" in case else "clean")
            noise = np.random.default_rng(20000 + seed).normal(0.0, 0.00002, len(times))
            if "noise" not in case:
                noise[:] = 0
            np.savez_compressed(
                trace_dir / f"{case}-{seed}.npz", times=times, noise=noise, observations=records
            )
            for reference in ("oracle", "ruckig_j100"):
                rp, rv, _ = references(records, times, reference)
                for mode, name in enumerate(
                    (
                        "true_velocity_diagnostic",
                        "nominal_dt",
                        "actual_dt",
                        "actual_dt_lowpass100Hz",
                    )
                ):
                    qs, metrics = run(times, rp, rv, 0.0, 20.0, False, 0.00005, mode, noise)
                    mask = times >= 2
                    rows.append(
                        {
                            "case": case,
                            "seed": seed,
                            "reference": reference,
                            "feedback": name,
                            "jerk_rms": float(metrics[0]),
                            "jerk_peak": float(metrics[1]),
                            "tracking_rms": float(metrics[2]),
                            "tracking_peak": float(metrics[3]),
                            "torque_rms": float(metrics[4]),
                            "saturation_seconds": float(metrics[5]),
                            **phase_metrics(times[mask], qs[mask]),
                        }
                    )
                    if seed == 0 and case == "jitter_noise":
                        _, refined = run(times, rp, rv, 0.0, 20.0, False, 0.000025, mode, noise)
                        rel = abs(refined[:5] - metrics[:5]) / np.maximum(abs(refined[:5]), 1e-10)
                        convergence.append(
                            {
                                "reference": reference,
                                "feedback": name,
                                "max_relative_change": float(max(rel)),
                                "passes_one_percent": bool(max(rel) < 0.01),
                            }
                        )
            print(json.dumps({"feedback_case": case, "seed": seed}), flush=True)
    result = {
        "status": "complete",
        "source_hashes": hashes,
        "runs": rows,
        "convergence": convergence,
        "all_convergence_checks_pass": bool(convergence)
        and all(x["passes_one_percent"] for x in convergence),
        "assumptions": {
            "nominal_hz": 1000,
            "jitter": "uniform integer ticks16..24 at50us per tick",
            "encoder_noise_std_rad": 0.00002,
            "plant": "same rigid motor with2ms actuator as tremor.py",
            "feedback": "PD Kp100 Kd18; no integral term; true state measured only in labeled diagnostic",
            "timing": "actual sample intervals known exactly; timestamp uncertainty not included",
            "measurement": "same position noise trace used for proportional and derivative terms across methods",
        },
        "novelty": "Classical correctly discretized differentiation and low-pass filtering; no novelty claimed.",
    }
    (root / "feedback-results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps({"runs": len(rows), "convergence": result["all_convergence_checks_pass"]}),
        flush=True,
    )


if __name__ == "__main__":
    main()
