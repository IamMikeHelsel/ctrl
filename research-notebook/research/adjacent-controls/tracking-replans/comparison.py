#!/usr/bin/env python3
"""Finite, deterministic actual-plant comparison. Numerical evidence only.

Run with the existing Python environment (numpy and scipy are required):
  python3 comparison.py
No software is installed. Outputs: comparison-results.json/.csv, comparison-trace.json,
comparison.svg, and comparison.pdf when the existing plot environment is available.
Use --render to regenerate the vector figure from saved numerical results.
"""
from fractions import Fraction as F
from pathlib import Path
import csv
import hashlib
import html
import json
import math
import platform
import subprocess
import sys
import numpy as np

ROOT = Path(__file__).resolve().parent
PROFILES = {
    "short_high_jerk": (F(10), F(1, 50)),
    "long_high_jerk": (F(10), F(1, 4)),
    "slow_precision": (F(1, 20), F(1, 2)),
}
COEFFICIENTS = ("zero_jerk_ff", "nominal_rate", "reciprocal_midpoint")
RATES = ("fixed_8", "fixed_10", "fixed_12", "aligned_smooth_stress")
W_VALUES = (F(0), F(1, 2000))
SIGMAS = (1, 10)
COLORS = {"zero_jerk_ff": "#ac493e", "nominal_rate": "#aa7a16", "reciprocal_midpoint": "#087f8c"}
LABELS = {"zero_jerk_ff": "Acceleration FF only", "nominal_rate": "Nominal-rate jerk FF", "reciprocal_midpoint": "Reciprocal-midpoint FF"}


def coefficient(name, sigma):
    return {"zero_jerk_ff": F(0), "nominal_rate": F(1, 10*sigma),
            "reciprocal_midpoint": F(5, 48*sigma)}[name]


def reference_segments(jerk, duration):
    t, state = F(0), (F(0), F(0), F(0))
    stages = []
    for sign in (1, -1, -1, 1):
        j = sign*jerk
        stages.append((t, duration, state, j))
        q, v, a = state
        state = (q+v*duration+a*duration**2/2+j*duration**3/6,
                 v+a*duration+j*duration**2/2, a+j*duration)
        t += duration
    assert state[1:] == (F(0), F(0))
    assert state[0] == 2*jerk*duration**3
    stages.append((t, F(4), state, F(0)))
    return stages


def rate(t, sigma, name, h):
    if name.startswith("fixed_"):
        return sigma*int(name.split("_")[1])
    return sigma*(10-2*math.tanh(4*math.cos(math.pi*t/(2*h))))


def disturbance(t, w):
    return -w*(-math.expm1(-20*t))


def integrate(profile, sigma, rate_name, w_bound, method, refined):
    from scipy.integrate import solve_ivp
    J, h = PROFILES[profile]
    kappa = coefficient(method, sigma)
    delta = max(abs(kappa-F(1, 8*sigma)), abs(kappa-F(1, 12*sigma)))
    radius = (w_bound+delta*J)/(2*sigma*sigma)
    stages = reference_segments(J, h)
    initial = np.zeros(3)
    blocks = []
    nfev = 0
    for start_f, duration_f, state_f, j_f in stages:
        start, duration, j = float(start_f), float(duration_f), float(j_f)
        q0, v0, a0 = map(float, state_f)

        def ref(t):
            s = t-start
            return q0+v0*s+a0*s*s/2+j*s**3/6, v0+a0*s+j*s*s/2, a0+j*s

        def rhs(t, physical):
            q, v_ref, a_ref = ref(t)
            ex, ev, ea = physical-np.array((q, v_ref, a_ref))
            u = a_ref-8*sigma*sigma*ex-6*sigma*ev-ea/2+float(kappa)*j
            r = rate(t, sigma, rate_name, float(h))
            w = disturbance(t, float(w_bound))
            return physical[1], physical[2], r*(u+w-physical[2])

        step = min(float(h)/4, .05/sigma)/(2 if refined else 1)
        sol = solve_ivp(rhs, (start, start+duration), initial, method="DOP853",
                        rtol=2e-11 if refined else 2e-9,
                        atol=2e-14 if refined else 2e-12,
                        max_step=step, dense_output=True)
        assert sol.success, sol.message
        # Both sides of each command switch are retained in the numerical
        # samples. The physical state is continuous; the command may jump.
        times = np.linspace(start, start+duration, 1001 if j == 0 else 251)
        physical = sol.sol(times).T
        refs = np.array([ref(t) for t in times])
        error = physical-refs
        z = np.column_stack((error[:, 0], error[:, 0]+error[:, 1]/(4*sigma),
                             error[:, 0]+error[:, 1]/(2*sigma)+error[:, 2]/(16*sigma*sigma)))
        controls = refs[:, 2]-8*sigma*sigma*error[:, 0]-6*sigma*error[:, 1]-error[:, 2]/2+float(kappa)*j
        disturbances = np.array([disturbance(t, float(w_bound)) for t in times])
        rates = np.array([rate(t, sigma, rate_name, float(h)) for t in times])
        assert np.all(rates >= 8*sigma-1e-12) and np.all(rates <= 12*sigma+1e-12)
        assert np.all(abs(disturbances) <= float(w_bound)+1e-14)
        actual_jerks = rates*(controls+disturbances-physical[:, 2])
        blocks.append({"t": times, "physical": physical, "reference": refs, "error": error,
                       "z": z, "u": controls, "effective_u": controls+disturbances,
                       "jerk": actual_jerks, "r": rates})
        initial = sol.y[:, -1]
        nfev += sol.nfev
    combined = {key: np.concatenate([b[key] for b in blocks]) for key in blocks[0]}
    e, z = combined["error"], combined["z"]
    a_ref_bound = J*h
    authority_bound = a_ref_bound+24*sigma*sigma*radius+abs(kappa)*J+w_bound
    result = {
        "profile": profile, "sigma": sigma, "rate_signal": rate_name,
        "disturbance_bound_m_s2": float(w_bound), "method": method,
        "kappa_s_exact": str(kappa), "residual_delta_s_exact": str(delta),
        "sufficient_radius_m_exact": str(radius), "sufficient_radius_m": float(radius),
        "reference_jerk_bound_m_s3": float(J), "reference_segment_duration_s": float(h),
        "motion_duration_s": float(4*h), "total_horizon_s": float(4*h+4),
        "reference_final_position_m": float(2*J*h**3),
        "measured_peak_abs_position_error_m": float(np.max(abs(e[:, 0]))),
        "measured_peak_abs_velocity_error_m_s": float(np.max(abs(e[:, 1]))),
        "measured_peak_abs_acceleration_error_m_s2": float(np.max(abs(e[:, 2]))),
        "measured_max_cube_coordinate_m": float(np.max(abs(z))),
        "final_position_error_m": float(e[-1, 0]),
        "measured_peak_nominal_command_m_s2": float(np.max(abs(combined["u"]))),
        "measured_peak_effective_target_m_s2": float(np.max(abs(combined["effective_u"]))),
        "sufficient_effective_target_bound_m_s2": float(authority_bound),
        "measured_peak_actual_jerk_m_s3": float(np.max(abs(combined["jerk"]))),
        "sample_count": len(combined["t"]), "rhs_evaluations": nfev,
    }
    # Consistency checks against the separately proposed sufficient bound.
    # Passing sampled numerical checks is not a proof of that bound.
    assert result["measured_max_cube_coordinate_m"] <= float(radius)+2e-9
    assert result["measured_peak_effective_target_m_s2"] <= float(authority_bound)+2e-9
    if rate_name == "fixed_10" and method == "nominal_rate" and w_bound == 0:
        assert result["measured_peak_abs_position_error_m"] < 1e-9
    return result, combined


def make_svg(rows, traces):
    W, H = 1420, 1235
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
             '<title>Tracking bounds and numerical errors under matched replanning</title>',
             '<desc>Six logarithmic panels compare a sufficient invariant radius against sampled peak error. Two plots show finite actual-plant error. Numerical trajectories do not certify robustness.</desc>',
             '<rect width="100%" height="100%" fill="#f7f8fa"/>',
             '<style>text{font-family:Arial,Helvetica,sans-serif;fill:#233140}</style>']
    def txt(x, y, s, size=13, bold=False, anchor=None):
        a = '' if anchor is None else f' text-anchor="{anchor}"'
        parts.append(f'<text x="{x}" y="{y}" font-size="{size}" font-weight="{"bold" if bold else "normal"}"{a}>{html.escape(s)}</text>')
    txt(35, 38, "A tracking bound is not a measured tracking error", 26, True)
    txt(35, 65, "Actual scalar plant; continuous-state feedback; no saturation. Numerical traces are evidence, not certification.", 15)
    txt(35, 89, "Same reference and disturbance for all coefficients. σ = 10 assumes a 10× faster physical response band.", 14)
    for x, method in zip((35, 420, 855), COEFFICIENTS):
        parts.append(f'<line x1="{x}" x2="{x+28}" y1="115" y2="115" stroke="{COLORS[method]}" stroke-width="4"/>')
        txt(x+37, 120, LABELS[method], 14)
    txt(35, 149, "Top panels: cap = sufficient radius; dot = largest sampled position error across the four declared rate signals. Log scale, mm.", 14)
    plot_min, plot_max = -4, 3
    for row_index, sigma in enumerate(SIGMAS):
        for col, profile in enumerate(PROFILES):
            x0, y0 = 28+col*466, 167+row_index*282
            parts.append(f'<rect x="{x0}" y="{y0}" width="450" height="266" rx="10" fill="white" stroke="#d6dde5"/>')
            J, h = PROFILES[profile]
            txt(x0+15, y0+24, f'{profile.replace("_", " ")} · σ={sigma}', 16, True)
            txt(x0+15, y0+44, f'r ∈ [{8*sigma}, {12*sigma}]/s; J={float(J):g} m/s³; h={float(h):g} s', 12)
            px, py, pw, ph = x0+72, y0+58, 355, 160
            def yy(value_mm):
                return py+ph*(plot_max-math.log10(max(10**plot_min, value_mm)))/(plot_max-plot_min)
            for exponent in range(plot_min, plot_max+1):
                y = yy(10**exponent)
                parts.append(f'<line x1="{px}" y1="{y:.2f}" x2="{px+pw}" y2="{y:.2f}" stroke="#e6ebef"/>')
                txt(px-8, y+4, f'{10**exponent:g}', 11, anchor="end")
            for idx, method in enumerate(COEFFICIENTS):
                chosen = [r for r in rows if r["sigma"] == sigma and r["profile"] == profile
                          and r["method"] == method and r["disturbance_bound_m_s2"] == .0005]
                measured = max(r["measured_peak_abs_position_error_m"] for r in chosen)*1000
                radius = chosen[0]["sufficient_radius_m"]*1000
                x = px+(idx+.5)*pw/3
                ym, yr = yy(measured), yy(radius)
                color = COLORS[method]
                parts.append(f'<line x1="{x}" y1="{ym:.2f}" x2="{x}" y2="{yr:.2f}" stroke="{color}" stroke-width="2"/>')
                parts.append(f'<line x1="{x-14}" y1="{yr:.2f}" x2="{x+14}" y2="{yr:.2f}" stroke="{color}" stroke-width="3"/>')
                parts.append(f'<circle cx="{x}" cy="{ym:.2f}" r="4.2" fill="{color}"/>')
                txt(x, py+ph+18, ("κ=0", "κ=1/(10σ)", "κ=5/(48σ)")[idx], 12, anchor="middle")
            txt(x0+15, y0+252, "W=0.0005 m/s²; zero initial tracking error", 12)
    txt(35, 759, "A smaller certificate radius does not make one coefficient best for every trace", 20, True)
    for col, profile in enumerate(("short_high_jerk", "long_high_jerk")):
        x0, y0 = 28+col*700, 779
        parts.append(f'<rect x="{x0}" y="{y0}" width="684" height="326" rx="10" fill="white" stroke="#d6dde5"/>')
        txt(x0+15, y0+25, f'{profile.replace("_", " ")} · fixed r=12/s · W=0', 16, True)
        selected = [(m, traces[f'{profile}|1|fixed_12|0|{m}']) for m in COEFFICIENTS]
        horizon = float(4*PROFILES[profile][1])+1.5
        peak = max(abs(p[1])*1000 for _, data in selected for p in data if p[0] <= horizon)
        bound = max(1e-6, peak*1.1)
        px, py, pw, ph = x0+76, y0+50, 585, 205
        def point(t, e):
            return px+pw*t/horizon, py+ph*(bound-e*1000)/(2*bound)
        for tick in (-1, -.5, 0, .5, 1):
            y = point(0, tick*bound/1000)[1]
            parts.append(f'<line x1="{px}" y1="{y:.2f}" x2="{px+pw}" y2="{y:.2f}" stroke="#e6ebef"/>')
            txt(px-8, y+4, f'{tick*bound:.3g}', 11, anchor="end")
        for tick in range(5):
            t = horizon*tick/4
            x = point(t, 0)[0]
            txt(x, py+ph+18, f'{t:.2f}', 11, anchor="middle")
        for method, data in selected:
            points = ' '.join(f'{x:.2f},{y:.2f}' for t, e in data if t <= horizon for x, y in [point(t, e)])
            parts.append(f'<polyline points="{points}" fill="none" stroke="{COLORS[method]}" stroke-width="2.2"/>')
        txt(px-50, py-8, "error (mm)", 11)
        txt(px+pw/2, py+ph+35, "time (s)", 12, anchor="middle")
        txt(x0+15, y0+313, "Here midpoint jerk FF has 1.25× nominal-FF error (linear model, same forcing).", 12)
    txt(35, 1141, "Sufficient tubes cover every admitted rate and disturbance in the theorem; plotted errors sample four chosen rate signals.", 14, True)
    txt(35, 1167, "The large short-pulse gap exposes conservatism. σ=10 changes the assumed plant; it is not a gain-only upgrade.", 14)
    txt(35, 1193, "No robot, VLA, flexible/contact, sampled-feedback, or hardware performance claim. See JSON/CSV for all 144 runs and refinement checks.", 13)
    parts.append('</svg>')
    return '\n'.join(parts)+'\n'


def main():
    import scipy
    rows, traces, animation = [], {}, {}
    for profile in PROFILES:
        for sigma in SIGMAS:
            for rate_name in RATES:
                for w in W_VALUES:
                    for method in COEFFICIENTS:
                        coarse, coarse_data = integrate(profile, sigma, rate_name, w, method, False)
                        fine, fine_data = integrate(profile, sigma, rate_name, w, method, True)
                        difference = np.max(abs(coarse_data["physical"]-fine_data["physical"]), axis=0)
                        assert difference[0] < 1e-8 and difference[1] < 1e-7 and difference[2] < 1e-6, difference
                        fine["refinement_max_position_difference_m"] = float(difference[0])
                        fine["refinement_max_velocity_difference_m_s"] = float(difference[1])
                        fine["refinement_max_acceleration_difference_m_s2"] = float(difference[2])
                        fine["refinement_peak_position_error_difference_m"] = abs(fine["measured_peak_abs_position_error_m"]-coarse["measured_peak_abs_position_error_m"])
                        rows.append(fine)
                        if sigma == 1 and rate_name == "fixed_12" and w == 0 and profile != "slow_precision":
                            key = f'{profile}|{sigma}|{rate_name}|{w}|{method}'
                            traces[key] = [[float(t), float(e)] for t, e in zip(fine_data["t"], fine_data["error"][:, 0])]
                        if sigma == 10 and rate_name == "aligned_smooth_stress" and w == F(1, 2000) and profile == "short_high_jerk":
                            motion_end = float(4*PROFILES[profile][1])
                            sample_times = np.unique(np.concatenate((np.linspace(0, motion_end, 81),
                                np.linspace(motion_end, motion_end+.2, 61),
                                np.linspace(motion_end+.2, fine["total_horizon_s"], 61))))
                            q = np.interp(sample_times, fine_data["t"], fine_data["reference"][:, 0])
                            x = np.interp(sample_times, fine_data["t"], fine_data["physical"][:, 0])
                            animation[method] = {"metrics": fine, "samples": [
                                {"t_s": float(t), "q_m": float(qi), "x_m": float(xi),
                                 "error_m": float(xi-qi), "R_m": fine["sufficient_radius_m"]}
                                for t, qi, xi in zip(sample_times, q, x)]}
            print(f'{profile}, sigma={sigma}: completed 24 paired integrations', flush=True)
    assert len(rows) == 144
    # The fixed-r=12, zero-disturbance linear error system scales exactly with
    # residual forcing. This checks the objective-specific comparison numerically.
    for profile in ("short_high_jerk", "long_high_jerk"):
        a = np.array(traces[f'{profile}|1|fixed_12|0|nominal_rate'])[:, 1]
        b = np.array(traces[f'{profile}|1|fixed_12|0|reciprocal_midpoint'])[:, 1]
        assert np.max(abs(b-1.25*a)) < 1e-9
    report = {
        "scope": "Deterministic numerical actual-plant comparison; no empirical certification or physical hardware claim.",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "runtime": {"python": platform.python_version(), "numpy": np.__version__, "scipy": scipy.__version__},
        "units": "SI in data; millimetres on figure.",
        "plant": "x'=v, v'=a, a'=r(t)(u+w-a). Continuous-state feedback; no saturation, delay, sensor error, friction or flexible modes.",
        "controller": "u=q''-8*sigma^2*(x-q)-6*sigma*(v-q')-(a-q'')/2+kappa*j.",
        "sigma_contract": "sigma=1 and 10 are different plant families: r in [8*sigma,12*sigma]. They use identical physical reference histories.",
        "reference": "Exact-rational initial reference state (0,0,0); four analytic constant-jerk segments [+J,-J,-J,+J], each of duration h, then 4 s constant hold. Position, velocity and acceleration match at boundaries; jerk may jump.",
        "profiles": {p: {"J_m_s3_exact": str(j), "h_s_exact": str(h), "final_position_m_exact": str(2*j*h**3)} for p, (j,h) in PROFILES.items()},
        "rate_signals": {"fixed": [8,10,12], "aligned_smooth_stress": "sigma*(10-2*tanh(4*cos(pi*t/(2*h))))", "stress_scope": "Smooth, bounded, hand-chosen to bias residual over signed jerk segments; not a proven worst-case adversary. No rate-of-change bound is assumed."},
        "disturbance": "w(t)=-W*(1-exp(-20*t)); W in {0,0.0005} m/s^2; smooth, |w|<=W. Same signal for each coefficient.",
        "sufficient_radius": "(W+delta*J)/(2*sigma^2), delta=max(|kappa-1/(8*sigma)|,|kappa-1/(12*sigma)|). Initial tracking error is zero.",
        "authority": "The reported sufficient target bound is max|q''|+24*sigma^2*R+|kappa|J+W. It is not an actuator model or calibrated limit.",
        "integration": {"method": "DOP853, separate solve per jerk segment", "coarse_rtol": 2e-9, "coarse_atol": 2e-12, "fine_rtol": 2e-11, "fine_atol": 2e-14, "coarse_max_step_s": "min(h/4,0.05/sigma)", "fine_max_step_s": "half coarse", "samples": "251 per nonzero-jerk segment; 1001 during terminal hold; both sides of switches retained", "limits": "Sampled maxima and numerical refinement cannot certify all continuous times or all possible uncertainties."},
        "run_count": len(rows), "paired_integrations": 2*len(rows),
        "max_refinement_position_difference_m": max(r["refinement_max_position_difference_m"] for r in rows),
        "validation": ["Exact rational reference splice continuity and terminal rest", "Sampled rate and disturbance envelopes", "Refined sampled trajectory comparisons", "Known-rate exact-tracking numerical witness", "Fixed-r=12 residual scaling numerical check", "Sampled compatibility with separately stated sufficient bounds"],
        "rows": rows,
        "figure_trace_data": traces,
    }
    (ROOT/"comparison-results.json").write_text(json.dumps(report, indent=2)+'\n')
    (ROOT/"comparison-trace.json").write_text(json.dumps({
        "scope": "Illustrative numerical trajectory, not a physical measurement or certified numerical enclosure.",
        "sigma": 10, "actual_rate_band_per_s": [80,120],
        "reference": "Four matched 20 ms segments with jerk [10,-10,-10,10] m/s^3; initial q=q'=q''=0; final constant reference 0.00016 m.",
        "rate_signal": "10*(10-2*tanh(4*cos(pi*t/0.04))) per second; hand-chosen smooth stress, not an optimal adversary.",
        "disturbance": "-0.0005*(1-exp(-20*t)) m/s^2.",
        "controller": report["controller"], "units": "SI; R is a sufficient position-error radius, not measured error.",
        "sampling": "201 times concentrated around the 80 ms reference motion; linearly interpolated from dense numerical output samples. Use analytical reference for exact animation geometry.",
        "methods": animation}, indent=2)+'\n')
    with (ROOT/"comparison-results.csv").open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    (ROOT/"comparison.svg").write_text(make_svg(rows, traces))
    plot_python = ROOT.parents[2]/".tools"/"travel-plot-python"/"bin"/"python"
    if plot_python.exists():
        subprocess.run([str(plot_python), str(Path(__file__).resolve()), "--render"], check=True)
    print(f'144 cases; 288 integrations; max position refinement difference {report["max_refinement_position_difference_m"]:.3g} m')


def render_matplotlib():
    """Render the same vector figure to SVG and PDF without importing scipy."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    report = json.loads((ROOT/"comparison-results.json").read_text())
    rows, traces = report["rows"], report["figure_trace_data"]
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                         "axes.titlesize": 12, "svg.hashsalt": "tracking-replans-v1"})
    fig = plt.figure(figsize=(14.2, 12.35), facecolor="#f7f8fa")
    fig.text(.025, .976, "A tracking bound is not a measured tracking error", fontsize=21, weight="bold")
    fig.text(.025, .953, "Actual scalar plant; continuous-state feedback; no saturation. Numerical traces are evidence, not certification.", fontsize=12)
    fig.text(.025, .932, "Same reference and disturbance across coefficients. σ = 10 assumes a 10× faster physical response band.", fontsize=12)
    handles = [Line2D([0],[0], color=COLORS[m], lw=3, label=LABELS[m]) for m in COEFFICIENTS]
    fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(.5,.922), ncol=3, frameon=False)
    fig.text(.025, .880, "Top panels: cap = sufficient radius; dot = largest sampled error across four declared rate signals. Log scale in mm.", fontsize=11)
    gs = fig.add_gridspec(2,3,left=.075,right=.975,top=.820,bottom=.450,hspace=.80,wspace=.30)
    names = {"short_high_jerk":"Short high jerk", "long_high_jerk":"Long high jerk", "slow_precision":"Slow precision"}
    for row_index, sigma in enumerate(SIGMAS):
        for col, profile in enumerate(PROFILES):
            ax = fig.add_subplot(gs[row_index,col])
            J, h = PROFILES[profile]
            ax.set_title(f'{names[profile]} · σ={sigma}\nr ∈ [{8*sigma},{12*sigma}]/s; J={float(J):g} m/s³; h={float(h):g} s', loc="left", pad=9)
            ax.set_yscale('log')
            ax.set_ylim(1e-4,1e3)
            ax.set_yticks([10.**i for i in range(-4,4)])
            ax.set_yticklabels(['.0001','.001','.01','.1','1','10','100','1000'], fontsize=9)
            ax.grid(axis='y', color='#e0e6eb')
            ax.set_xlim(-.5,2.5)
            ax.set_xticks([0,1,2])
            ax.set_xticklabels(['κ=0','κ=1/(10σ)','κ=5/(48σ)'],fontsize=10)
            for idx, method in enumerate(COEFFICIENTS):
                chosen = [r for r in rows if r['sigma']==sigma and r['profile']==profile and r['method']==method and r['disturbance_bound_m_s2']==.0005]
                measured = max(r['measured_peak_abs_position_error_m'] for r in chosen)*1000
                radius = chosen[0]['sufficient_radius_m']*1000
                ax.plot([idx,idx],[measured,radius],color=COLORS[method],lw=1.8)
                ax.plot(idx,radius,marker='_',markersize=24,markeredgewidth=2.6,color=COLORS[method])
                ax.plot(idx,measured,marker='o',markersize=5.5,color=COLORS[method])
            ax.text(0,-.24,'W=0.0005 m/s²; zero initial error',transform=ax.transAxes,fontsize=9)
    fig.text(.025,.393,'A smaller certificate radius does not make a coefficient best for every trace',fontsize=16,weight='bold')
    gs2=fig.add_gridspec(1,2,left=.075,right=.975,top=.349,bottom=.143,wspace=.25)
    for col,profile in enumerate(('short_high_jerk','long_high_jerk')):
        ax=fig.add_subplot(gs2[0,col])
        horizon=float(4*PROFILES[profile][1])+1.5
        for method in COEFFICIENTS:
            data=np.array(traces[f'{profile}|1|fixed_12|0|{method}'])
            chosen=data[:,0]<=horizon
            ax.plot(data[chosen,0],1000*data[chosen,1],color=COLORS[method],lw=1.8)
        ax.set_title(f'{names[profile]} · r=12/s · W=0',loc='left',pad=9)
        ax.set_xlabel('time (s)')
        ax.set_ylabel('position error (mm)')
        ax.set_xlim(0,horizon)
        ax.grid(color='#e0e6eb')
        ax.text(0,-.29,'Midpoint jerk FF has 1.25× nominal-FF error here.\nLinear model, identical forcing; no universal ranking.',transform=ax.transAxes,fontsize=10)
    fig.text(.025,.058,'The sufficient tube covers the stated model uncertainty; plotted peaks sample only the declared signals.',fontsize=11,weight='bold')
    fig.text(.025,.038,'The short-pulse gap exposes conservatism. Faster response is a plant assumption, not a gain-only upgrade.',fontsize=11)
    fig.text(.025,.018,'No robot, VLA, contact, sampled-feedback, or hardware performance claim. JSON/CSV contain all 144 cases and refinement checks.',fontsize=10)
    fig.savefig(ROOT/'comparison.svg', metadata={'Date':None})
    fig.savefig(ROOT/'comparison.pdf', metadata={'CreationDate':None,'ModDate':None,'Title':'Tracking bounds and numerical errors under matched replanning'})
    plt.close(fig)
    # A layout-only render may follow the numerical run. Preserve both revisions;
    # do not imply that new integrations ran when only presentation changed.
    report.setdefault("numerical_execution_source_sha256", report["source_sha256"])
    report["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report["render_provenance"] = {
        "matplotlib": matplotlib.__version__,
        "scope": "Final script hash above; numerical execution revision retained separately. Since that run, only documentation, layout, and result-summary/render metadata changed. Numerical model, integration, validation and trace extraction did not change."
    }
    report["selected_comparison"] = {
        "selection": "For each listed profile, sigma and coefficient, maximum sampled position error across the four declared rate signals with W=0.0005 m/s^2. Same reference, initial error and disturbance for each coefficient; no optimal-adversary claim.",
        "rows": [
            {"profile": profile, "sigma": sigma, "method": method,
             "largest_sampled_error_across_four_rates_m": max(r["measured_peak_abs_position_error_m"] for r in rows if r["profile"] == profile and r["sigma"] == sigma and r["method"] == method and r["disturbance_bound_m_s2"] == .0005),
             "sufficient_radius_m": next(r["sufficient_radius_m"] for r in rows if r["profile"] == profile and r["sigma"] == sigma and r["method"] == method and r["disturbance_bound_m_s2"] == .0005)}
            for profile, sigma in (("short_high_jerk", 1), ("long_high_jerk", 10))
            for method in COEFFICIENTS]
    }
    (ROOT/"comparison-results.json").write_text(json.dumps(report, indent=2)+'\n')
    print(f'Vector SVG/PDF rendered with matplotlib {matplotlib.__version__}',flush=True)


if __name__ == "__main__":
    render_matplotlib() if '--render' in sys.argv else main()
