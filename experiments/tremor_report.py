# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib>=3.10,<4", "numpy==2.5.4"]
# ///
"""Reproducible paired scoring and scientific figure for the saved tremor probes."""

import json
import statistics as stats
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path("work/vision")
vision = json.loads((ROOT / "tremor-results.json").read_text())
feedback = json.loads((ROOT / "feedback-results.json").read_text())


def compare(a, b):
    return {
        "jerk_reduction_percent": 100 * (1 - a["jerk_rms"] / b["jerk_rms"]),
        "tracking_ratio": a["tracking_rms"] / b["tracking_rms"],
        "lag_difference_ms": a["phase_lag_ms"] - b["phase_lag_ms"],
        "gate": a["jerk_rms"] <= 0.8 * b["jerk_rms"]
        and a["tracking_rms"] <= 1.05 * b["tracking_rms"]
        and abs(a["phase_lag_ms"] - b["phase_lag_ms"]) <= 1
        and a["saturation_seconds"] <= b["saturation_seconds"] + 1e-10,
    }


def summarize(rows):
    reductions = [x["jerk_reduction_percent"] for x in rows]
    return {
        "pairs": len(rows),
        "gate_passes": sum(x["gate"] for x in rows),
        "mean_jerk_reduction_percent": stats.mean(reductions),
        "range_jerk_reduction_percent": [min(reductions), max(reductions)],
        "pairs_raw": rows,
    }


v = {(r["case"], r["seed"], r["method"]): r for r in vision["robot"]["runs"]}
f = {(r["case"], r["seed"], r["reference"], r["feedback"]): r for r in feedback["runs"]}
analysis = {
    "gate": ">=20% jerk reduction, <=5% worse tracking, abs lag difference<=1ms, no increased saturation",
    "novelty": "None claimed for robotics; timestamp correction and low-pass filtering are established.",
    "camera_actual_vs_nominal": {},
    "feedback_actual_vs_nominal": {},
    "freshness_all_pairings": [],
}
for case in ("camera_jitter", "camera_jitter_noise", "servo_jitter", "queue_loss"):
    analysis["camera_actual_vs_nominal"][case] = summarize(
        [
            compare(v[case, seed, "extrap_actual"], v[case, seed, "extrap_nominal"])
            for seed in range(10)
        ]
    )
for case in ("jitter", "noise", "jitter_noise"):
    for ref in ("oracle", "ruckig_j100"):
        analysis["feedback_actual_vs_nominal"][f"{case}/{ref}"] = summarize(
            [
                compare(f[case, seed, ref, "actual_dt"], f[case, seed, ref, "nominal_dt"])
                for seed in range(10)
            ]
        )
for case in ("queue_loss", "blackout"):
    for j in (30, 100, 300):
        for baseline_j in (30, 100, 300):
            analysis["freshness_all_pairings"].append(
                {
                    "case": case,
                    "candidate_jerk": j,
                    "baseline_jerk": baseline_j,
                    **summarize(
                        [
                            compare(
                                v[case, seed, f"fresh_j{j}"], v[case, seed, f"ruckig_j{baseline_j}"]
                            )
                            for seed in range(10)
                        ]
                    ),
                }
            )
(ROOT / "tremor-analysis.json").write_text(json.dumps(analysis, indent=2) + "\n")

fig, axes = plt.subplots(1, 2, figsize=(12, 5.2), layout="constrained")
colors = ["#c96b27", "#246fbc", "#3f9467"]
for ax, rows, cases, names, key, filters in [
    (
        axes[0],
        feedback["runs"],
        ["clean", "jitter", "noise", "jitter_noise"],
        ["nominal_dt", "actual_dt", "actual_dt_lowpass100Hz"],
        "feedback",
        {"reference": "oracle"},
    ),
    (
        axes[1],
        vision["robot"]["runs"],
        ["clean", "camera_jitter", "noise_only", "camera_jitter_noise"],
        ["extrap_nominal", "extrap_actual", "ruckig_j100"],
        "method",
        {},
    ),
]:
    group = defaultdict(list)
    for r in rows:
        if all(r[k] == value for k, value in filters.items()):
            group[r["case"], r[key]].append(r["jerk_rms"])
    for i, name in enumerate(names):
        vals = [group[case, name] for case in cases]
        means = np.array([stats.mean(x) for x in vals])
        err = np.array(
            [
                [m - min(x) for m, x in zip(means, vals, strict=True)],
                [max(x) - m for m, x in zip(means, vals, strict=True)],
            ]
        )
        ax.bar(
            np.arange(4) + (i - 1) * 0.25,
            means,
            0.23,
            yerr=err,
            capsize=3,
            label=name.replace("_", " "),
            color=colors[i],
        )
    ax.set_xticks(range(4), ["Clean", "Timing jitter", "Noise only", "Jitter + noise"])
    ax.set_yscale("log")
    ax.set_ylabel("Motor RMS jerk (rad/s³), logarithmic scale")
    ax.grid(axis="y", alpha=0.2)
    ax.set_axisbelow(True)
    ax.legend(fontsize=8)
axes[0].set_title("1 kHz feedback differentiation\nIdeal continuous reference; same PD gains")
axes[1].set_title("60 Hz visual target reconstruction\nIdeal joint feedback; Ruckig adds lag")
fig.suptitle(
    "Timing errors can create tremor; measurement noise survives clock correction", fontsize=14
)
fig.supxlabel(
    "Synthetic 10 s trials; ranges over 10 paired seeds (clean: 1). Established methods, not a hardware or novelty claim.",
    fontsize=9,
)
fig.savefig(ROOT / "tremor-summary.png", dpi=180)
print(
    json.dumps(
        {
            "camera": {
                k: v["mean_jerk_reduction_percent"]
                for k, v in analysis["camera_actual_vs_nominal"].items()
            },
            "feedback": {
                k: v["mean_jerk_reduction_percent"]
                for k, v in analysis["feedback_actual_vs_nominal"].items()
            },
            "freshness_gate_wins": sum(
                x["gate_passes"] for x in analysis["freshness_all_pairings"]
            ),
        }
    )
)
