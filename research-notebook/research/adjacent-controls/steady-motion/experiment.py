#!/usr/bin/env python3
"""Deterministic target-decision replay. No plant or executed-motion model.

Run: python3 experiment.py
Writes results.json and comparison.svg beside this source. Standard library only.
Truth, noise, the dwell policy, and the gate use exact Fraction arithmetic.
The one-pole filter and plot use floating-point arithmetic.
"""

from fractions import Fraction as F
from pathlib import Path
import hashlib
import html
import json
import math

ROOT = Path(__file__).resolve().parent
DT = F(1, 50)
END = F(3)
EPS = F(1, 2000)
THRESHOLD = F(1, 500)
DWELL = F(1, 10)
TAU = F(1, 20)
CHANGE = F(17, 25)
ACQUIRE_TOL = F(3, 4000)
ONSET = F(3, 4000)
METHODS = ("raw", "dwell_100ms", "lowpass_50ms", "gate_2mm")
LABELS = {
    "raw": "Raw replacement",
    "dwell_100ms": "Minimum dwell: 100 ms",
    "lowpass_50ms": "One-pole filter: 50 ms",
    "gate_2mm": "Strict gate: 2 mm",
}
COLORS = {
    "raw": "#bf4b45", "dwell_100ms": "#8c64ad",
    "lowpass_50ms": "#b17c12", "gate_2mm": "#087f8c",
}


def truth(case, t):
    if case == "fixed_hold":
        return F(0)
    if case == "step_20mm":
        return F(1, 50) if t >= CHANGE else F(0)
    if case == "slow_drift_3mm":
        return F(3, 1000) * min(F(1), max(F(0), (t-F(1, 2))/2))
    if case == "small_move_1mm":
        return F(1, 1000) if t >= CHANGE else F(0)
    raise ValueError(case)


CASES = {
    "fixed_hold": {
        "title": "Fixed hold: noise can be ignored",
        "ylim_mm": [-0.8, 0.8],
        "event_s": None,
        "hold_windows": [("settled_hold", F(1, 2), END)],
        "note": "Gate target stays fixed. Filtering reduces noise, but its target still changes.",
    },
    "step_20mm": {
        "title": "20 mm step: large changes pass the gate",
        "ylim_mm": [-1.5, 22],
        "event_s": CHANGE,
        "hold_windows": [("before_step", F(0), F(1, 2)),
                         ("after_step", F(3, 2), END)],
        "note": "Gate selects immediately; the selected target retains a 0.5 mm bias.",
    },
    "slow_drift_3mm": {
        "title": "3 mm slow drift: commitment creates lag",
        "ylim_mm": [-0.8, 4],
        "event_s": F(1, 2),
        "hold_windows": [("before_drift", F(0), F(2, 5)),
                         ("after_drift", F(27, 10), END)],
        "note": "Gate waits, jumps once, and ends 0.97 mm short of the true target.",
    },
    "small_move_1mm": {
        "title": "1 mm intentional move: the gate misses it",
        "ylim_mm": [-0.8, 2],
        "event_s": CHANGE,
        "hold_windows": [("before_step", F(0), F(1, 2)),
                         ("after_step", F(3, 2), END)],
        "note": "A low-jitter score can hide task failure: the gate never selects this move.",
    },
}


def variation(values, initial=F(0)):
    total = 0
    previous = initial
    for value in values:
        total += abs(value-previous)
        previous = value
    return total


def error_stats(values, targets, indices):
    errors = [float(values[k])-float(targets[k]) for k in indices]
    return {
        "sample_count": len(errors),
        "max_abs_error_m": max(abs(e) for e in errors),
        "rms_error_m": math.sqrt(sum(e*e for e in errors)/len(errors)),
        "mean_error_m": sum(errors)/len(errors),
    }


def timing(values, targets, times, event):
    if event is None:
        return {"onset_delay_s": None, "acquisition_delay_s": None,
                "status": "not_applicable_to_fixed_hold"}
    # Onset means a selected target >=0.75 mm from the zero initial target.
    # This threshold exceeds the 0.5 mm observation error. It is not arm onset.
    eligible = [i for i, t in enumerate(times) if t >= event]
    onset = next((i for i in eligible if float(values[i]) >= float(ONSET)), None)
    # Acquisition is meaningful after a deliberate response and once the final
    # intended target has become constant. This prevents an overlap between
    # tolerance bands from counting as response to the small intentional move.
    final_target = targets[-1]
    final_start = len(targets)-1
    while final_start > 0 and targets[final_start-1] == final_target:
        final_start -= 1
    good_suffix = True
    acquisition = None
    for i in reversed(eligible):
        good_suffix &= abs(float(values[i])-float(final_target)) <= float(ACQUIRE_TOL)+1e-14
        if good_suffix and onset is not None and i >= onset and i >= final_start:
            acquisition = i
    return {
        "onset_delay_s": None if onset is None else float(times[onset]-event),
        "acquisition_delay_s": None if acquisition is None else float(times[acquisition]-event),
        "final_target_established_s": float(times[final_start]),
        "acquisition_delay_after_final_target_s": None if acquisition is None else float(times[acquisition]-times[final_start]),
        "status": "not_acquired_in_test" if acquisition is None else "sampled_target_acquired",
    }


def replay(case, config, dt=DT):
    times = [i*dt for i in range(int(END/dt)+1)]
    targets = [truth(case, t) for t in times]
    proposals = [p + (EPS if i % 2 == 0 else -EPS) for i, p in enumerate(targets)]
    output = {m: [] for m in METHODS}
    selected = {m: F(0) for m in METHODS}
    last_dwell = -DWELL
    alpha = 1-math.exp(-float(dt/TAU))
    # An initial held anchor exists before sample 0. All methods receive sample
    # 0 and update by their stated policy; the filter gets its usual alpha step.
    accepted_c = [F(0)]
    accepted_p = [F(0)]
    accepted_at = []
    gate_checks = []
    for k, (t, p, y) in enumerate(zip(times, targets, proposals)):
        selected["raw"] = y
        if t-last_dwell >= DWELL:
            selected["dwell_100ms"] = y
            last_dwell = t
        selected["lowpass_50ms"] = float(selected["lowpass_50ms"]) + alpha*(float(y)-float(selected["lowpass_50ms"]))
        old = selected["gate_2mm"]
        accept = abs(y-old) > THRESHOLD
        selected["gate_2mm"] = y if accept else old
        assert abs(y-p) <= EPS
        assert abs(selected["gate_2mm"]-p) <= THRESHOLD+EPS
        if abs(p-old) > THRESHOLD+EPS:
            assert accept
        if abs(old-p) <= EPS:
            assert not accept  # H >= 2 epsilon.
        if accept:
            accepted_c.append(y)
            accepted_p.append(p)
            accepted_at.append(t)
        gate_checks.append({"accepted": accept, "proposal_distance_m": float(abs(y-old))})
        for method in METHODS:
            output[method].append(selected[method])

    n = len(accepted_at)
    tv_p_accepted = variation(accepted_p[1:], accepted_p[0])
    tv_c_accepted = variation(accepted_c[1:], accepted_c[0])
    tv_p_all = variation(targets)
    assert all(abs(c-p) <= EPS for c, p in zip(accepted_c, accepted_p))
    assert all(abs(b-a) > THRESHOLD for a, b in zip(accepted_c, accepted_c[1:]))
    assert n*(THRESHOLD-2*EPS) <= tv_p_accepted
    assert tv_c_accepted*(THRESHOLD-2*EPS) <= THRESHOLD*tv_p_accepted
    assert tv_p_accepted <= tv_p_all
    assert variation(output["gate_2mm"]) == tv_c_accepted
    if case == "fixed_hold":
        assert n == 0
    if case == "small_move_1mm":
        assert n == 0
    if case == "step_20mm":
        assert accepted_at[0] == CHANGE

    metrics = {}
    for method, values in output.items():
        previous = 0.0
        changes = 0
        for value in values:
            changes += abs(float(value)-previous) > 1e-14
            previous = float(value)
        windows = {}
        for name, lo, hi in config["hold_windows"]:
            idx = [i for i, t in enumerate(times) if lo <= t <= hi]
            assert len(set(targets[i] for i in idx)) == 1
            windows[name] = {"start_s": float(lo), "end_s": float(hi),
                             **error_stats(values, targets, idx)}
        metrics[method] = {
            "target_total_variation_m": float(variation(values)),
            "target_change_count": changes,
            "all_samples_error": error_stats(values, targets, range(len(times))),
            "hold_windows": windows,
            "final_target_m": float(values[-1]),
            "final_error_m": float(values[-1])-float(targets[-1]),
            **timing(values, targets, times, config["event_s"]),
        }
    exact_checks = {
        "status": "passed_exact_fraction_checks",
        "accepted_update_count": n,
        "accepted_true_target_variation_m_exact": str(tv_p_accepted),
        "accepted_selected_target_variation_m_exact": str(tv_c_accepted),
        "full_true_target_variation_m_exact": str(tv_p_all),
        "count_upper_bound_exact": str(tv_p_accepted/(THRESHOLD-2*EPS)),
        "target_variation_upper_bound_m_exact": str(THRESHOLD*tv_p_accepted/(THRESHOLD-2*EPS)),
        "selected_error_bound_m_exact": str(THRESHOLD+EPS),
        "accepted_times_s_exact": [str(t) for t in accepted_at],
        "checks": ["bounded_observation_error", "fixed_valid_anchor_rejects_noise",
                   "distinguishable_change_passes", "selected_target_error_bound",
                   "accepted_steps_strictly_exceed_threshold", "finite_switch_count",
                   "finite_target_variation", "accepted_truth_variation_le_full_variation"],
    }
    return {
        "title": config["title"], "truth_definition": case,
        "true_target_total_variation_m": float(tv_p_all),
        "metrics": metrics, "exact_gate_checks": exact_checks,
        "samples": [{"t_s": float(t), "truth_m": float(p), "proposal_m": float(y),
                     **{m: float(output[m][i]) for m in METHODS},
                     "gate_accepted": gate_checks[i]["accepted"]}
                    for i, (t, p, y) in enumerate(zip(times, targets, proposals))],
    }


def svg(results):
    W, H = 1240, 955
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
             '<title>Target steadiness versus response: four deterministic examples</title>',
             '<desc>Target decisions only, before motion feasibility. A threshold removes bounded noise, but delays slow drift and ignores small intended motion.</desc>',
             '<rect width="100%" height="100%" fill="#f6f7f8"/>',
             '<style>text{font-family:Arial,Helvetica,sans-serif;fill:#233140} .small{font-size:13px} .axis{font-size:12px;fill:#566272}</style>']
    def text(x, y, value, size=14, weight="normal", fill=None):
        color = '' if fill is None else f' fill="{fill}"'
        parts.append(f'<text x="{x}" y="{y}" font-size="{size}" font-weight="{weight}"{color}>{html.escape(value)}</text>')
    text(40, 40, "Steady targets have a price", 27, "bold")
    text(40, 67, "Target selection only. No plant, robot, jerk, contact, or VLA performance model.", 16)
    text(40, 92, "50 Hz proposals • alternating ±0.5 mm error • 2 mm strict gate • independently specified true target", 14)
    legend = [("truth", "True target", "#293542")]+[(m, LABELS[m], COLORS[m]) for m in METHODS]
    lx = [40, 215, 405, 660, 930]
    for (key, label, color), x in zip(legend, lx):
        dash = ' stroke-dasharray="6 4"' if key == "truth" else ''
        parts.append(f'<line x1="{x}" y1="120" x2="{x+25}" y2="120" stroke="{color}" stroke-width="3"{dash}/>')
        text(x+33, 125, label, 13)
    for index, (case, config) in enumerate(CASES.items()):
        col, row = index % 2, index // 2
        x0, y0 = 34+col*606, 150+row*350
        plot_x, plot_y, pw, ph = x0+58, y0+50, 510, 195
        low, high = config["ylim_mm"]
        parts.append(f'<rect x="{x0}" y="{y0}" width="586" height="330" rx="12" fill="white" stroke="#d7dee5"/>')
        text(x0+18, y0+28, config["title"], 17, "bold")
        def point(t, value):
            return plot_x+float(t)/float(END)*pw, plot_y+(high-value)/(high-low)*ph
        for j in range(5):
            value = low+(high-low)*j/4
            yy = point(0, value)[1]
            parts.append(f'<line x1="{plot_x}" y1="{yy:.2f}" x2="{plot_x+pw}" y2="{yy:.2f}" stroke="#e8edf1"/>')
            text(plot_x-43, yy+4, f"{value:.1f}", 12)
        for t in range(4):
            xx = point(t, 0)[0]
            parts.append(f'<line x1="{xx:.2f}" y1="{plot_y}" x2="{xx:.2f}" y2="{plot_y+ph}" stroke="#e8edf1"/>')
            text(xx-4, plot_y+18+ph, str(t), 12)
        text(plot_x-40, plot_y-10, "mm", 12)
        text(plot_x+pw/2-23, plot_y+33+ph, "time (s)", 12)
        clip = f'clip{index}'
        parts.append(f'<defs><clipPath id="{clip}"><rect x="{plot_x}" y="{plot_y}" width="{pw}" height="{ph}"/></clipPath></defs>')
        data = results[case]["samples"]
        for method in METHODS:
            # Vertical transitions show target replacements. These are not a
            # claim that a physical arm moves in zero time.
            path = []
            prev = 0.0
            for k, sample in enumerate(data):
                xx, yy = point(sample["t_s"], sample[method]*1000)
                if k == 0:
                    path.append(f'M {xx:.2f} {point(0, 0)[1]:.2f}')
                path.append(f'L {xx:.2f} {point(sample["t_s"], prev*1000)[1]:.2f}')
                path.append(f'L {xx:.2f} {yy:.2f}')
                prev = sample[method]
            width = 2.7 if method == "gate_2mm" else 1.4
            opacity = .65 if method == "raw" else .9
            parts.append(f'<path d="{" ".join(path)}" fill="none" stroke="{COLORS[method]}" stroke-width="{width}" opacity="{opacity}" clip-path="url(#{clip})"/>')
        truth_path = []
        for k, sample in enumerate(data):
            xx, yy = point(sample["t_s"], sample["truth_m"]*1000)
            if k == 0:
                truth_path.append(f'M {xx:.2f} {yy:.2f}')
            else:
                old_y = point(sample["t_s"], data[k-1]["truth_m"]*1000)[1]
                truth_path.append(f'L {xx:.2f} {old_y:.2f} L {xx:.2f} {yy:.2f}')
        parts.append(f'<path d="{" ".join(truth_path)}" fill="none" stroke="#293542" stroke-width="1.8" stroke-dasharray="6 4" clip-path="url(#{clip})"/>')
        text(x0+18, y0+294, config["note"], 12)
        metrics = results[case]["metrics"]
        tv = " / ".join(f'{metrics[m]["target_total_variation_m"]*1000:.1f}' for m in METHODS)
        text(x0+18, y0+315, f"Variation (raw / dwell / filter / gate): {tv} mm", 12)
    text(40, 874, "The gate removes pure noise here. It does not prove physical steadiness or task completion.", 16, "bold")
    text(40, 900, "This 50 Hz plot is one trace. At 100 and 200 Hz, dwell aliases exact alternation to a constant; see cadence sensitivity in results.json.", 13)
    text(40, 925, "Hold-error windows, response criteria, exact checks, and full traces are in results.json. Reproduce with experiment.py.", 13)
    parts.append('</svg>')
    return '\n'.join(parts)+'\n'


def main():
    results = {case: replay(case, config) for case, config in CASES.items()}
    sensitivity = {}
    for hz in (50, 100, 200):
        runs = results if hz == 50 else {case: replay(case, config, F(1, hz)) for case, config in CASES.items()}
        sensitivity[str(hz)] = {
            "sample_rate_hz": hz, "alternating_noise_frequency_hz": hz/2,
            "samples_per_dwell": int(DWELL*hz),
            "cases": {case: {"metrics": run["metrics"], "exact_gate_checks": run["exact_gate_checks"]}
                      for case, run in runs.items()},
        }
    report = {
        "title": "Target-layer commitment experiment",
        "scope": "Synthetic target decisions before motion feasibility; no plant, robot, executed command, jerk, contact, or VLA performance claim.",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "units": "SI: position in metres, time in seconds. SVG uses millimetres for readability.",
        "parameters": {"dt_s": float(DT), "duration_s": float(END), "epsilon_m": float(EPS),
                       "threshold_m": float(THRESHOLD), "dwell_s": float(DWELL), "tau_s": float(TAU),
                       "lowpass_alpha": 1-math.exp(-float(DT/TAU)), "initial_selected_target_m": 0},
        "definitions": {
            "noise": "Exactly +epsilon at even sample indices and -epsilon at odd indices.",
            "dwell": "Accept latest proposal when at least 100 ms passed since the last dwell acceptance; first proposal accepted at t=0.",
            "lowpass": "y[k]=y[k-1]+(1-exp(-dt/tau))*(proposal[k]-y[k-1]); initial y[-1]=0. Standard sampled one-pole recursion.",
            "gate": "Accept proposal iff abs(proposal-anchor)>H; otherwise retain anchor. This does not run motion-feasibility checks.",
            "variation": "Sum of absolute changes in selected targets, including change from initial target 0 to the first selected target.",
            "onset": "First post-event selected target >=0.75 mm above initial 0; delay from event. A target-decision threshold, not physical onset.",
            "acquisition": "First sample at or after onset and after the final intended target becomes constant, such that every remaining selected target is within 0.75 mm of that final truth. Delay is reported from the event and from establishment of the final target. Finite sampled test only.",
            "hold_windows": "Closed time windows listed in each method's metrics. Truth is constant on each window; max and RMS errors are sampled.",
            "sample_phase": "Main plot is 50 Hz. Separate exact replays at 100 and 200 Hz expose parity sensitivity: dwell spans 5, 10, and 20 samples respectively. Even parity aliases the alternating noise to a constant. Noise frequency also changes with cadence, so this is not a same-continuous-disturbance experiment or universal performance ranking.",
        },
        "truth_definitions": {
            "fixed_hold": "0 m for all 3 s.",
            "step_20mm": "0 m until 0.68 s, then 0.020 m.",
            "slow_drift_3mm": "0 m until 0.5 s; linear 0.0015 m/s ramp to 0.003 m at 2.5 s; hold thereafter.",
            "small_move_1mm": "0 m until 0.68 s, then 0.001 m.",
        },
        "method_order": list(METHODS),
        "cases": results,
        "cadence_sensitivity": sensitivity,
        "tradeoffs": [
            "Raw targets track bounded-noise truth closely but change at every proposal.",
            "Minimum dwell reduces update count; it does not eliminate target jumps or guarantee smooth physical motion.",
            "Low-pass filtering reduces alternating noise but delays transitions and retains residual oscillation.",
            "The strict gate rejects all fixed-hold noise here and accepts the large step; it delays slow drift and ignores the intentional 1 mm move.",
            "Gate count and variation bounds use variation of true targets at acceptance times; they do not bound robot path length.",
        ],
        "verification": "Exact Fraction assertions passed for all gate conditions, error bounds, accepted-history variation and count inequalities. Filter metrics and SVG are floating-point numerical output.",
    }
    (ROOT/"results.json").write_text(json.dumps(report, indent=2)+'\n')
    (ROOT/"comparison.svg").write_text(svg(results))
    for case, result in results.items():
        print(case)
        for method in METHODS:
            m = result["metrics"][method]
            print(f'  {method}: variation={1000*m["target_total_variation_m"]:.3f} mm; '
                  f'onset={m["onset_delay_s"]}; acquisition={m["acquisition_delay_s"]}; '
                  f'final_error={1000*m["final_error_m"]:.3f} mm')
        print('  exact gate checks passed')


if __name__ == "__main__":
    main()
