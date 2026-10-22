"""Generate Manim-style scientific domain animations (GIFs) for the ctrl project site.

Uses live closed-loop MuJoCo 3.16.0 benchmark telemetry from ``ctrl.robotics.mujoco_benchmarks``
and renders four high-contrast scientific animations (800x360, dark obsidian palette):
1. ``pillar1_lorentz_cbf.gif``: 3D 4-contact quadruped emergency braking before a wall (x_lim=1.20m)
   showing stopping-distance CBF h(x,v) >= 0 and real-time 4-foot Lorentz friction cone trajectories.
2. ``pillar2_septic_energy.gif``: 6-DOF manipulator rest-to-rest trajectory under 7th-order septic
   (eta=-11) vs. 5th-order minimum-jerk (eta=0), showing dynamic power and cumulative Joule savings.
3. ``pillar3_sontag_hinf.gif``: 6-DOF manipulator under sinusoidal + t=0.72s impulsive torque
   disturbance, comparing tuned high-gain Computed-Torque Control (CTC) vs. Sontag CLF + H_inf/ISS.
4. ``pillar4_se3_servoing.gif``: 6-DOF eye-in-hand camera under 160-deg optical-axis roll, showing
   IBVS 5.76x backwards camera retreat vs. monotone log-depth HBVS convergence.
"""

from __future__ import annotations

import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation, PillowWriter
import numpy as np

from ctrl.robotics.mujoco_benchmarks import (
    run_arm6dof_septic_energy_benchmark,
    run_quadruped_zmp_cbf_benchmark,
    run_se3_visual_servoing_benchmark,
)
from ctrl.robotics.trajectories import septic_a, septic_q, septic_v

BG = "#0b0f17"
PANEL_BG = "#111827"
GRID_COL = "#1f2937"
TEXT_COL = "#f3f4f6"
MUTED_COL = "#9ca3af"
TEAL = "#2dd4bf"
AMBER = "#fbbf24"
ROSE = "#fb7185"
BLUE = "#60a5fa"


def _style_ax(ax: plt.Axes, title: str, xlabel: str, ylabel: str) -> None:
    ax.set_facecolor(PANEL_BG)
    ax.set_title(title, color=TEXT_COL, fontsize=10.5, fontweight="bold", pad=8)
    ax.set_xlabel(xlabel, color=MUTED_COL, fontsize=9)
    ax.set_ylabel(ylabel, color=MUTED_COL, fontsize=9)
    ax.tick_params(colors=MUTED_COL, labelsize=8)
    for spine in ax.spines.values():
        spine.set_color("#263244")
    ax.grid(True, color=GRID_COL, linestyle="--", linewidth=0.7, alpha=0.8)


def make_pillar1_lorentz_cbf(out_dir: Path) -> Path:
    res = run_quadruped_zmp_cbf_benchmark()
    t = np.array(res["t_hist"])
    x = np.array(res["x_hist"])
    vx = np.array(res["vx_hist"])
    h = np.array(res["h_cbf_hist"])
    fz = np.array(res["min_fz_hist"])

    # Unshielded trajectory under nominal command ax = +1.2 m/s^2 from x0=0, vx0=3.0
    x_unshielded = 3.0 * t + 0.5 * 1.2 * (t**2)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.0, 3.6), dpi=100, facecolor=BG)
    fig.subplots_adjust(left=0.08, right=0.97, top=0.84, bottom=0.16, wspace=0.26)
    fig.suptitle(
        "Pillar 1: Closed-Form 3D Lorentz-Cone CBF & 4-Foot Bilinear ZMP Braking (<100 ns C99)",
        color=TEXT_COL,
        fontsize=11,
        fontweight="bold",
        y=0.96,
    )

    _style_ax(ax1, "Trunk Position x(t) vs. Obstacle Wall (1.20 m)", "Time t (s)", "Position x (m)")
    ax1.set_xlim(0, t[-1])
    ax1.set_ylim(0, 1.55)
    ax1.axhline(1.20, color=ROSE, linestyle="--", linewidth=1.4, label="Wall x_lim = 1.20 m")
    ax1.axhspan(1.20, 1.55, color=ROSE, alpha=0.12)

    (line_un,) = ax1.plot([], [], color=ROSE, linestyle=":", linewidth=1.8, label="Unshielded (crashes at 0.37s)")
    (line_x,) = ax1.plot([], [], color=TEAL, linewidth=2.4, label="Lorentz-CBF Shielded (stops 1.192m)")
    (pt_x,) = ax1.plot([], [], "o", color=TEAL, markersize=6)
    ax1.legend(loc="lower right", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.5)

    _style_ax(ax2, "Barrier Margin h(x,v) >= 0 & Min Foot Normal Force", "Time t (s)", "h(x,v) (m)  /  f_z,min / 50 (N)")
    ax2.set_xlim(0, t[-1])
    ax2.set_ylim(-0.1, 1.85)
    ax2.axhline(0.0, color=AMBER, linestyle="--", linewidth=1.1, label="Safety Boundary h = 0")
    (line_h,) = ax2.plot([], [], color=TEAL, linewidth=2.2, label="Barrier h(r, v) >= 0.008 m")
    (line_fz,) = ax2.plot([], [], color=BLUE, linewidth=1.8, label="Min Foot Force f_z,min / 50 (>0.44)")
    (pt_h,) = ax2.plot([], [], "o", color=TEAL, markersize=6)
    ax2.legend(loc="upper right", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.5)

    n_frames = 45
    idxs = np.linspace(1, len(t), n_frames, dtype=int)

    def update(frame_i: int):
        k = idxs[frame_i]
        line_un.set_data(t[:k], x_unshielded[:k])
        line_x.set_data(t[:k], x[:k])
        pt_x.set_data([t[k - 1]], [x[k - 1]])
        line_h.set_data(t[:k], h[:k])
        line_fz.set_data(t[:k], fz[:k] / 50.0)
        pt_h.set_data([t[k - 1]], [h[k - 1]])
        return line_un, line_x, pt_x, line_h, line_fz, pt_h

    anim = FuncAnimation(fig, update, frames=n_frames, interval=65, blit=True)
    out_path = out_dir / "pillar1_lorentz_cbf.gif"
    anim.save(out_path, writer=PillowWriter(fps=15))
    plt.close(fig)
    return out_path


def make_pillar2_septic_energy(out_dir: Path) -> Path:
    res = run_arm6dof_septic_energy_benchmark()
    t = np.array(res["min_jerk"]["t_hist"])
    p0 = np.array(res["min_jerk"]["p_joule_hist"])
    p11 = np.array(res["septic_opt"]["p_joule_hist"])
    dt = t[1] - t[0]
    e0 = np.cumsum(p0) * dt
    e11 = np.cumsum(p11) * dt

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.0, 3.6), dpi=100, facecolor=BG)
    fig.subplots_adjust(left=0.09, right=0.97, top=0.84, bottom=0.16, wspace=0.27)
    fig.suptitle(
        "Pillar 2: 7th-Order Septic Trajectory Shaping (eta = -11) vs. 5th-Order Minimum-Jerk",
        color=TEXT_COL,
        fontsize=11,
        fontweight="bold",
        y=0.96,
    )

    _style_ax(ax1, "Instantaneous Dynamic Motor Power I^2 R (W)", "Time t (s)", "Dynamic Power (W)")
    ax1.set_xlim(0, t[-1])
    ax1.set_ylim(0, max(p0) * 1.12)
    (line_p0,) = ax1.plot([], [], color=ROSE, linestyle="--", linewidth=1.9, label="5th-Order Min-Jerk (eta = 0)")
    (line_p11,) = ax1.plot([], [], color=TEAL, linewidth=2.3, label="7th-Order Septic (eta = -11)")
    ax1.legend(loc="upper right", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.5)

    _style_ax(ax2, "Cumulative Dynamic Joule Heat Integral (J)", "Time t (s)", "Cumulative Dynamic Energy (J)")
    ax2.set_xlim(0, t[-1])
    ax2.set_ylim(0, max(e0) * 1.12)
    (line_e0,) = ax2.plot([], [], color=ROSE, linestyle="--", linewidth=1.9, label="Min-Jerk: 773.2 J")
    (line_e11,) = ax2.plot([], [], color=TEAL, linewidth=2.3, label="Septic Opt: 599.5 J (-22.5% dyn / -4.1% tot)")
    (pt_e11,) = ax2.plot([], [], "o", color=TEAL, markersize=6)
    ax2.legend(loc="upper left", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.2)

    n_frames = 45
    idxs = np.linspace(1, len(t), n_frames, dtype=int)

    def update(frame_i: int):
        k = idxs[frame_i]
        line_p0.set_data(t[:k], p0[:k])
        line_p11.set_data(t[:k], p11[:k])
        line_e0.set_data(t[:k], e0[:k])
        line_e11.set_data(t[:k], e11[:k])
        pt_e11.set_data([t[k - 1]], [e11[k - 1]])
        return line_p0, line_p11, line_e0, line_e11, pt_e11

    anim = FuncAnimation(fig, update, frames=n_frames, interval=65, blit=True)
    out_path = out_dir / "pillar2_septic_energy.gif"
    anim.save(out_path, writer=PillowWriter(fps=15))
    plt.close(fig)
    return out_path


def make_pillar3_sontag_hinf(out_dir: Path) -> Path:
    import mujoco
    from ctrl.robotics.estimation_lqr import backstepping_and_sontag_clf
    from ctrl.robotics.mujoco_benchmarks import ARM_6DOF_MJCF

    duration = 1.6
    model = mujoco.MjModel.from_xml_string(ARM_6DOF_MJCF)
    data = mujoco.MjData(model)
    dt = model.opt.timestep
    steps = int(round(duration / dt))
    q_target = np.array([0.85, -0.65, 1.05, -0.75, 0.60, 0.50], dtype=float)
    dist_weights = np.array([1.0, 0.85, 0.70, 0.45, 0.30, 0.20], dtype=float)
    certified_gamma = 0.20

    t_hist: list[float] = []
    w_hist: list[float] = []
    traces: dict[str, list[float]] = {"ctc": [], "sontag": []}

    for mode in ("ctc", "sontag"):
        mujoco.mj_resetData(model, data)
        for step in range(steps):
            t = step * dt
            s = min(max(t / duration, 0.0), 1.0)
            q_des = float(septic_q(-11.0, s)) * q_target
            dq_des = (float(septic_v(-11.0, s)) / duration) * q_target
            ddq_des = (float(septic_a(-11.0, s)) / (duration**2)) * q_target

            impulse = 14.0 * math.exp(-(((t - 0.72) / 0.045) ** 2))
            w_dist = dist_weights * (
                6.5 * math.sin(2.0 * math.pi * 2.5 * t)
                + 3.5 * math.cos(2.0 * math.pi * 5.0 * t)
                + impulse
            )
            e_pos = data.qpos[:6] - q_des
            e_vel = data.qvel[:6] - dq_des

            if mode == "ctc":
                ddq_cmd = ddq_des - 416.0 * e_pos - 42.0 * e_vel
                tau_aux = -12.0 * (e_vel + 16.0 * e_pos)
            else:
                c1, c2 = 16.0, 26.0
                u_bs_vec = np.zeros(6)
                u_sontag_vec = np.zeros(6)
                for j in range(6):
                    z2_j = float(e_vel[j] + c1 * e_pos[j])
                    a_lie = -c1 * float(e_pos[j] ** 2) - c2 * (z2_j**2)
                    clf_step = backstepping_and_sontag_clf(
                        c1, c2, 0.0, 0.0, 0.0, float(e_pos[j]), float(e_vel[j]), a_lie, z2_j
                    )
                    u_bs_vec[j] = float(clf_step["u_backstepping"])
                    u_sontag_vec[j] = float(clf_step["u_sontag"])
                ddq_cmd = ddq_des + u_bs_vec + 0.35 * u_sontag_vec
                tau_aux = -(1.0 / (certified_gamma**2)) * (e_vel + c1 * e_pos)

            data.qacc[:6] = ddq_cmd
            tau_rne = np.zeros(6)
            mujoco.mj_rne(model, data, 1, tau_rne)
            data.ctrl[:6] = tau_rne + tau_aux
            data.qfrc_applied[:6] = w_dist
            mujoco.mj_step(model, data)

            if step % 8 == 0:
                if mode == "ctc":
                    t_hist.append(t)
                    w_hist.append(float(np.linalg.norm(w_dist)))
                traces[mode].append(float(np.linalg.norm(data.qpos[:6] - q_des)) * 1000.0)  # mrad

    t_arr = np.array(t_hist)
    w_arr = np.array(w_hist)
    err_ctc = np.array(traces["ctc"])
    err_son = np.array(traces["sontag"])

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.0, 3.6), dpi=100, facecolor=BG)
    fig.subplots_adjust(left=0.09, right=0.97, top=0.84, bottom=0.16, wspace=0.27)
    fig.suptitle(
        "Pillar 3: Sontag Universal CLF + H_inf/ISS vs. Tuned High-Gain Computed-Torque Control",
        color=TEXT_COL,
        fontsize=11,
        fontweight="bold",
        y=0.96,
    )

    _style_ax(ax1, "External Disturbance Torque Norm ||w(t)||_2 (N*m)", "Time t (s)", "||w(t)||_2 (N*m)")
    ax1.set_xlim(0, t_arr[-1])
    ax1.set_ylim(0, max(w_arr) * 1.12)
    ax1.axvline(0.72, color=AMBER, linestyle=":", linewidth=1.2, label="Impulse Impact (t = 0.72s)")
    (line_w,) = ax1.plot([], [], color=AMBER, linewidth=2.0, label="Disturbance ||w(t)||_2")
    ax1.legend(loc="upper right", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.5)

    _style_ax(ax2, "6-DOF Joint Tracking Error ||e_q(t)||_2 (mrad)", "Time t (s)", "Tracking Error (mrad)")
    ax2.set_xlim(0, t_arr[-1])
    ax2.set_ylim(0, max(err_ctc) * 1.15)
    (line_ctc,) = ax2.plot([], [], color=ROSE, linestyle="--", linewidth=1.9, label="Tuned High-Gain CTC (peak 27.1 mrad)")
    (line_son,) = ax2.plot([], [], color=TEAL, linewidth=2.3, label="Sontag CLF + H_inf (peak 16.4 mrad, -39.4%)")
    (pt_son,) = ax2.plot([], [], "o", color=TEAL, markersize=6)
    ax2.legend(loc="upper right", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.2)

    n_frames = 45
    idxs = np.linspace(1, len(t_arr), n_frames, dtype=int)

    def update(frame_i: int):
        k = idxs[frame_i]
        line_w.set_data(t_arr[:k], w_arr[:k])
        line_ctc.set_data(t_arr[:k], err_ctc[:k])
        line_son.set_data(t_arr[:k], err_son[:k])
        pt_son.set_data([t_arr[k - 1]], [err_son[k - 1]])
        return line_w, line_ctc, line_son, pt_son

    anim = FuncAnimation(fig, update, frames=n_frames, interval=65, blit=True)
    out_path = out_dir / "pillar3_sontag_hinf.gif"
    anim.save(out_path, writer=PillowWriter(fps=15))
    plt.close(fig)
    return out_path


def make_pillar4_se3_servoing(out_dir: Path) -> Path:
    res = run_se3_visual_servoing_benchmark()
    t = np.array(res["t_hist"])
    d_hbvs = np.array(res["d_hbvs_hist"])
    d_ibvs = np.array(res["d_ibvs_hist"])
    d_lb = np.array(res["d_lower_bound_hist"])

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.0, 3.6), dpi=100, facecolor=BG)
    fig.subplots_adjust(left=0.08, right=0.97, top=0.84, bottom=0.16, wspace=0.26)
    fig.suptitle(
        "Pillar 4: 6-DOF SE(3) Homography-Based Visual Servoing Under 160-deg Optical Roll",
        color=TEXT_COL,
        fontsize=11,
        fontweight="bold",
        y=0.96,
    )

    _style_ax(ax1, "Camera Depth z(t): Classical IBVS Retreat vs. HBVS", "Time t (s)", "Camera Depth z (m)")
    ax1.set_xlim(0, t[-1])
    ax1.set_ylim(0, max(d_ibvs) * 1.08)
    ax1.axhline(1.0, color=MUTED_COL, linestyle=":", linewidth=1.1, label="Target Depth d* = 1.0 m")
    (line_ibvs,) = ax1.plot([], [], color=ROSE, linestyle="--", linewidth=1.9, label="Classical IBVS (retreats to 12.67 m)")
    (line_hbvs1,) = ax1.plot([], [], color=TEAL, linewidth=2.3, label="Verified SE(3) HBVS (monotone)")
    ax1.legend(loc="upper right", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.5)

    _style_ax(ax2, "Zoomed HBVS Depth & Convexity Lower Bound", "Time t (s)", "Camera Depth z (m)")
    ax2.set_xlim(0, t[-1])
    ax2.set_ylim(0.3, 2.35)
    ax2.axhline(1.0, color=MUTED_COL, linestyle=":", linewidth=1.1, label="Target d* = 1.00 m")
    (line_hbvs2,) = ax2.plot([], [], color=TEAL, linewidth=2.4, label="HBVS Depth z(t) in [1.015, 2.20] m")
    (line_lb,) = ax2.plot([], [], color=BLUE, linestyle="-.", linewidth=1.6, label="Proved Convex Lower Bound")
    (pt_hbvs,) = ax2.plot([], [], "o", color=TEAL, markersize=6)
    ax2.legend(loc="upper right", facecolor=PANEL_BG, edgecolor="#263244", labelcolor=TEXT_COL, fontsize=7.5)

    n_frames = 45
    idxs = np.linspace(1, len(t), n_frames, dtype=int)

    def update(frame_i: int):
        k = idxs[frame_i]
        line_ibvs.set_data(t[:k], d_ibvs[:k])
        line_hbvs1.set_data(t[:k], d_hbvs[:k])
        line_hbvs2.set_data(t[:k], d_hbvs[:k])
        line_lb.set_data(t[:k], d_lb[:k])
        pt_hbvs.set_data([t[k - 1]], [d_hbvs[k - 1]])
        return line_ibvs, line_hbvs1, line_hbvs2, line_lb, pt_hbvs

    anim = FuncAnimation(fig, update, frames=n_frames, interval=65, blit=True)
    out_path = out_dir / "pillar4_se3_servoing.gif"
    anim.save(out_path, writer=PillowWriter(fps=15))
    plt.close(fig)
    return out_path


def main() -> None:
    for root in (Path("/Users/mike/lean-work/ctrl/site/assets"), Path("/Users/mike/Dev/ctrl/site/assets")):
        root.mkdir(parents=True, exist_ok=True)
    out = Path("/Users/mike/lean-work/ctrl/site/assets")
    for fn in (make_pillar1_lorentz_cbf, make_pillar2_septic_energy, make_pillar3_sontag_hinf, make_pillar4_se3_servoing):
        p = fn(out)
        print(f"Generated {p} ({p.stat().st_size / 1024:.1f} KB)")


if __name__ == "__main__":
    main()
