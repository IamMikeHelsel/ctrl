#!/usr/bin/env python3
"""One fixed numerical illustration of the normalized TravelSafety model.

Run from the workspace root:
  .tools/travel-plot-python/bin/python publication/plot_travel_example.py

Dependencies used for the original render: numpy 2.5.4, matplotlib 3.11.2.
The exact analytic held solution is evaluated in float64; no ODE time-stepper
or parameter search is used. The resulting finite grid is not a safety proof.
"""
from __future__ import annotations

import datetime as dt
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import math
from pathlib import Path
import platform
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
IMAGES = HERE / "manuscript/images"
P_RATIONAL = [
    ["38/5", "257/25", "5"],
    ["257/25", "1319/50", "769/50"],
    ["5", "769/50", "278/25"],
]
P = np.array([[float(Fraction(q)) for q in row] for row in P_RATIONAL])
H_PATTERN = (Fraction(1, 20), Fraction(1, 5))
W_PATTERN = (Fraction(1, 100), Fraction(-1, 100))
FINAL_TIME = Fraction(20)
MAX_PLOT_DT = Fraction(1, 500)
INITIAL_STATE = np.array([0.0, 0.0, 1.0], dtype=np.float64)


def held_segment(elapsed: float, state: np.ndarray, held_input: float) -> np.ndarray:
    """SaturatedLag.heldSegment with state order position, velocity, acceleration."""
    x, v, a = state
    exp_minus_one = math.expm1(-elapsed)
    exponential = math.exp(-elapsed)
    return np.array(
        [
            x + elapsed * v + held_input * elapsed**2 / 2
            + (a - held_input) * (elapsed + exp_minus_one),
            v + held_input * elapsed + (a - held_input) * (-exp_minus_one),
            held_input + (a - held_input) * exponential,
        ],
        dtype=np.float64,
    )


def energy(state: np.ndarray) -> float:
    return float(state @ P @ state)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    IMAGES.mkdir(parents=True, exist_ok=True)
    state = INITIAL_STATE.copy()
    clock = Fraction(0)
    edges = [0.0]
    dense_time, dense_state = [], []
    requests, clipped, disturbances = [], [], []
    intervals = []
    n = 0
    while clock < FINAL_TIME:
        duration = H_PATTERN[n % len(H_PATTERN)]
        disturbance = W_PATTERN[n % len(W_PATTERN)]
        assert clock + duration <= FINAL_TIME
        request = float(-state[0] - 3 * state[1] - 2 * state[2])
        command = max(-1.0, min(1.0, request))
        held_input = command + float(disturbance)
        point_count = math.ceil(duration / MAX_PLOT_DT)
        for j in range(point_count):
            local_time = duration * Fraction(j, point_count)
            dense_time.append(float(clock + local_time))
            dense_state.append(held_segment(float(local_time), state, held_input))
        intervals.append(
            {
                "index": n,
                "start_time_rational": str(clock),
                "duration_rational": str(duration),
                "held_disturbance_rational": str(disturbance),
                "initial_state_float64": state.tolist(),
                "initial_energy_float64": energy(state),
                "requested_command_float64": request,
                "clipped_command_float64": command,
                "held_input_after_disturbance_float64": held_input,
            }
        )
        requests.append(request)
        clipped.append(command)
        disturbances.append(float(disturbance))
        state = held_segment(float(duration), state, held_input)
        clock += duration
        edges.append(float(clock))
        n += 1
    assert clock == FINAL_TIME
    dense_time.append(float(clock))
    dense_state.append(state)
    times = np.array(dense_time)
    states = np.array(dense_state)
    energies = np.einsum("ni,ij,nj->n", states, P, states)
    requests = np.array(requests)
    clipped = np.array(clipped)
    assert requests[0] == -2.0 and clipped[0] == -1.0
    assert abs(energies[0] - 278 / 25) < 1e-12
    assert np.all(np.isfinite(states)) and np.all(np.isfinite(energies))
    assert np.all(np.diff(times) > 0)
    # These finite-grid checks validate the plotted example, not the theorem.
    assert np.max(np.abs(states[:, 0])) <= 2
    assert np.max(energies) <= 12
    assert np.max(np.abs(clipped)) <= 1

    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 9,
            "axes.titlesize": 10,
            "axes.labelsize": 9,
            "legend.fontsize": 8,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.grid": True,
            "grid.alpha": 0.23,
            "grid.linewidth": 0.55,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )
    fig, axes = plt.subplots(3, 1, figsize=(7.2, 7.1), sharex=True)
    fig.subplots_adjust(left=0.105, right=0.97, bottom=0.17, top=0.87, hspace=0.32)
    fig.suptitle("A saturated actuator-lag trajectory with held disturbances", y=0.97, fontsize=12)
    fig.text(
        0.5, 0.928,
        r"$z_0=(0,0,1)$; periods $0.05,0.20$ repeat; held $w=+0.01,-0.01$ repeat",
        ha="center", fontsize=9,
    )
    blue, green, orange, bound = "#1f4e79", "#16775b", "#b35a18", "#a43f44"

    ax = axes[0]
    ax.plot(times, states[:, 0], color=blue, linewidth=1.7, label="Position")
    ax.axhline(2, color=bound, linestyle="--", linewidth=1.0, label=r"Certified travel limits $\pm2$")
    ax.axhline(-2, color=bound, linestyle="--", linewidth=1.0)
    ax.set_ylim(-2.35, 2.35)
    ax.set_ylabel("Position")
    ax.set_title("(a) Position and certified travel limits", loc="left")
    ax.legend(loc="upper right", frameon=True, facecolor="white", edgecolor="white", ncols=2)

    ax = axes[1]
    ax.plot(times, energies, color=blue, linewidth=1.7, label=r"Energy $z^\mathsf{T}Pz$")
    ax.axhline(12, color=bound, linestyle="--", linewidth=1.0, label="Certified sublevel 12")
    ax.scatter([0], [energies[0]], color=blue, s=15, zorder=4)
    ax.set_ylim(-0.45, 13.1)
    ax.set_ylabel("Energy")
    ax.set_title("(b) Quadratic energy", loc="left")
    ax.legend(loc="upper right", frameon=True, facecolor="white", edgecolor="white")

    ax = axes[2]
    ax.stairs(requests, edges, baseline=None, color=orange, linewidth=1.1, label="Sampled request (held)")
    ax.stairs(clipped, edges, baseline=None, color=green, linewidth=1.45, linestyle="--", label="Clipped command (held)")
    ax.scatter([0, 0], [-2, -1], color=[orange, green], s=19, zorder=5, clip_on=False)
    ax.annotate(
        "Initial request −2 → clipped −1", xy=(0.03, -1.45), xytext=(1.4, -1.95),
        fontsize=8, arrowprops={"arrowstyle": "->", "color": "#555555", "lw": 0.75},
    )
    ax.set_ylim(-2.3, 1.0)
    ax.set_ylabel("Command")
    ax.set_xlabel("Time (normalized units)")
    ax.set_title("(c) Saturation is active initially", loc="left")
    ax.legend(loc="upper right", frameon=False)
    ax.set_xlim(0, 20)
    ax.set_xticks(np.arange(0, 21, 2))

    fig.text(
        0.105, 0.055,
        "Numerical illustration, not a proof. Safety is proved in TravelSafety.lean.\n"
        "Exact held formulas evaluated in float64; disturbance is added after the clamp. All units normalized.",
        ha="left", va="center", fontsize=8, color="#444444", linespacing=1.5,
    )
    png = IMAGES / "travel-example.png"
    pdf = IMAGES / "travel-example.pdf"
    fig.savefig(png, dpi=220, facecolor="white")
    fig.savefig(
        pdf, facecolor="white",
        metadata={
            "Title": "Numerical illustration of the normalized TravelSafety model",
            "Subject": "A single deterministic trajectory; safety proof is in Lean, not this simulation",
            "Creator": "publication/plot_travel_example.py with matplotlib",
        },
    )
    plt.close(fig)

    ix = int(np.argmax(np.abs(states[:, 0])))
    ie = int(np.argmax(energies))
    max_values = {
        "dense_grid_max_abs_position": float(abs(states[ix, 0])),
        "dense_grid_max_abs_position_time": float(times[ix]),
        "dense_grid_max_energy": float(energies[ie]),
        "dense_grid_max_energy_time": float(times[ie]),
        "sampled_max_abs_requested_command": float(np.max(np.abs(requests))),
        "sampled_max_abs_clipped_command": float(np.max(np.abs(clipped))),
        "held_max_abs_disturbance": float(max(abs(x) for x in disturbances)),
        "clipping_active_intervals": int(np.count_nonzero(requests != clipped)),
        "final_state_float64": state.tolist(),
        "final_energy_float64": energy(state),
    }
    source_names = [
        "lean-controls/LeanControls/SaturatedLag.lean",
        "lean-controls/LeanControls/TravelSafety.lean",
        "lean-controls/LeanControls/TravelDisturbance.lean",
        "lean-controls/LeanControls/Generated/TravelQuarterLower.lean",
    ]
    artifact = {
        "status": "numerical illustration; not proof evidence",
        "generated_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "proof_source": "LeanControls.TravelSafety.travel_limit and active_initial_travel",
        "scope": "One deterministic execution of the normalized, exact-real held model, evaluated in float64. No parameter sweep or hardware validation.",
        "recipe": {
            "state_order": ["position", "velocity", "acceleration"],
            "initial_state_exact": ["0", "0", "1"],
            "P_exact": P_RATIONAL,
            "duration_pattern_exact": [str(x) for x in H_PATTERN],
            "disturbance_pattern_exact": [str(x) for x in W_PATTERN],
            "index_convention": "n starts at 0; patterns repeat by n modulo 2",
            "requested_input": "-x_n - 3*v_n - 2*a_n, computed at the sample and held",
            "clipped_input": "max(-1,min(1,requested_input))",
            "actual_held_input": "clipped_input + w_n; disturbance enters after the clamp",
            "exact_held_position": "x_n + t*v_n + u*t^2/2 + (a_n-u)*(t-1+exp(-t))",
            "exact_held_velocity": "v_n + u*t + (a_n-u)*(1-exp(-t))",
            "exact_held_acceleration": "u + (a_n-u)*exp(-t)",
            "evaluation": "float64 with math.exp and math.expm1; analytic segment endpoints define the recurrence; no ODE integrator",
            "final_time_exact": str(FINAL_TIME),
            "max_dense_grid_spacing_exact": str(MAX_PLOT_DT),
            "dense_grid_rule": "ceil(duration/max_spacing) evenly spaced local points excluding right endpoint; append final endpoint once; rational clock before float conversion",
            "interval_count": n,
            "dense_grid_point_count": len(times),
            "randomness": "none",
        },
        "observations": max_values,
        "observation_limit": "Dense-grid extrema are maxima over the finite evaluation grid, not certified continuous-time extrema. The analytic Lean theorem supplies universal safety.",
        "sample_intervals": intervals,
        "environment": {
            "python": sys.version,
            "platform": platform.platform(),
            "matplotlib": matplotlib.__version__,
            "numpy": np.__version__,
            "packages": {name: importlib.metadata.version(name) for name in
                         ["matplotlib", "numpy", "contourpy", "cycler", "fonttools", "kiwisolver", "packaging", "pillow", "pyparsing", "python-dateutil", "six"]},
        },
        "source_sha256": {name: sha256(ROOT / name) for name in source_names},
        "script_sha256": sha256(Path(__file__)),
        "outputs": {
            "pdf": {"path": str(pdf.relative_to(ROOT)), "sha256": sha256(pdf)},
            "png": {"path": str(png.relative_to(ROOT)), "sha256": sha256(png)},
        },
    }
    (HERE / "travel-illustration.json").write_text(json.dumps(artifact, indent=2) + "\n")
    print(json.dumps(max_values, indent=2))
    print(f"Saved {pdf.relative_to(ROOT)} and {png.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
