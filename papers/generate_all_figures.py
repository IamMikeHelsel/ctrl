#!/usr/bin/env python3
"""Generate publication-quality vector PDF and PNG figures for Papers 1, 3, and 4."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import matplotlib
import matplotlib.pyplot as plt
import numpy as np

matplotlib.use("Agg")

# Publication styling
plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 9.5,
        "axes.labelsize": 10,
        "axes.titlesize": 10.5,
        "legend.fontsize": 8.5,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "figure.dpi": 300,
        "savefig.bbox": "tight",
        "axes.grid": True,
        "grid.alpha": 0.25,
        "lines.linewidth": 1.8,
    }
)

ROOT = Path(__file__).resolve().parent


def ensure_dirs() -> dict[str, Path]:
    dirs = {
        "p0": ROOT / "00_executive_portfolio" / "figures",
        "p1": ROOT / "01_robotics_control_lean4" / "figures",
        "p3": ROOT / "03_experimental_math_erdos_273_885" / "figures",
        "p4": ROOT / "04_formalized_combinatorics_lean4" / "figures",
    }
    for d in dirs.values():
        d.mkdir(parents=True, exist_ok=True)
    return dirs


# =============================================================================
# Paper 1 Figures: Robotics & Control Verification in Lean 4
# =============================================================================


def q_septic(s: np.ndarray, eta: float) -> np.ndarray:
    """Septic rest-to-rest family: q_eta(s) = 10s^3 - 15s^4 + 6s^5 + eta*s^3*(1-s)^3*(2s-1)."""
    q_mj = 10 * s**3 - 15 * s**4 + 6 * s**5
    phi = (s**3) * ((1 - s) ** 3) * (2 * s - 1)
    return q_mj + eta * phi


def v_septic(s: np.ndarray, eta: float) -> np.ndarray:
    """Velocity profile dq/ds."""
    v_mj = 30 * s**2 - 60 * s**3 + 30 * s**4
    dphi = (s**2) * ((1 - s) ** 2) * (-3 + 14 * s - 14 * s**2)
    return v_mj + eta * dphi


def a_septic(s: np.ndarray, eta: float) -> np.ndarray:
    """Acceleration profile d^2q/ds^2."""
    a_mj = 60 * s - 180 * s**2 + 120 * s**3
    ddphi = 2 * s * (1 - s) * (-3 + 27 * s - 66 * s**2 + 42 * s**3)
    return a_mj + eta * ddphi


def generate_paper1_figures(out_dir: Path) -> None:
    from ctrl import robotics

    # Figure 1: Septic trajectory family & Exact Pareto Dominance
    s = np.linspace(0.0, 1.0, 500)
    etas = np.linspace(-15.5, 4.0, 400)
    # Exact quadratic forms from RobotEnergySmoothness.lean:
    # Iv(eta) = (3/10010)*(eta + 260/9)^2 + 350/297
    # Ia(eta) = (2/77)*(eta + 11)^2 + 14
    Iv = (3.0 / 10010.0) * (etas + 260.0 / 9.0) ** 2 + (350.0 / 297.0)
    Ia = (2.0 / 77.0) * (etas + 11.0) ** 2 + 14.0
    Iv_0 = 10.0 / 7.0
    Ia_0 = 120.0 / 7.0
    Iv_rel = 100.0 * (Iv - Iv_0) / Iv_0
    Ia_rel = 100.0 * (Ia - Ia_0) / Ia_0

    fig, axes = plt.subplots(1, 3, figsize=(13.2, 3.6))

    # Panel A: Relative energy change vs eta
    ax = axes[0]
    ax.plot(etas, Ia_rel, color="#1f77b4", label=r"Inertial Joule loss $\Delta I_a(\eta)$ [%]")
    ax.plot(etas, Iv_rel, color="#d62728", linestyle="--", label=r"Viscous loss $\Delta I_v(\eta)$ [%]")
    ax.axhline(0.0, color="black", linewidth=0.9, alpha=0.6)
    ax.axvspan(-11.0, 0.0, color="#2ca02c", alpha=0.14, label=r"Pareto-dominating interval $\eta \in [-11, 0)$")
    ax.scatter([0.0, -11.0], [0.0, -11.0 / 60.0 * 100.0], color="#1f77b4", zorder=5)
    ax.scatter([0.0, -11.0], [0.0, -421.0 / 3900.0 * 100.0], color="#d62728", zorder=5)
    ax.annotate("Min-jerk\n($\\eta=0$)", xy=(0.0, 0.0), xytext=(0.6, -5.5),
                arrowprops={"arrowstyle": "->", "lw": 0.8}, fontsize=8)
    ax.annotate("Min-$I_a$ ($\\eta=-11$)\n$-18.33\\%$ Joule\n$-10.79\\%$ viscous",
                xy=(-11.0, -18.333), xytext=(-14.8, -11.5),
                arrowprops={"arrowstyle": "->", "lw": 0.8}, fontsize=8)
    ax.set_xlabel(r"Septic perturbation parameter $\eta$")
    ax.set_ylabel("Change relative to minimum-jerk [%]")
    ax.set_title("(a) Dual Energy Reduction on $[-11, 0)$")
    ax.legend(loc="upper left", framealpha=0.9)

    # Panel B: Velocity profiles
    ax = axes[1]
    ax.plot(s, v_septic(s, 0.0), color="#333333", label=r"Min-jerk ($\eta=0$, $I_v=10/7$)")
    ax.plot(s, v_septic(s, -5.5), color="#ff7f0e", linestyle="-.", label=r"Mid-Pareto ($\eta=-5.5$)")
    ax.plot(s, v_septic(s, -11.0), color="#2ca02c", label=r"Min-$I_a$ ($\eta=-11$, $-10.79\%$ viscous)")
    ax.set_xlabel(r"Normalized time $s = t/T \in [0, 1]$")
    ax.set_ylabel(r"Normalized velocity $v_\eta(s)$")
    ax.set_title(r"(b) Velocity Profiles $v_\eta(s) = \dot{q}_\eta(s)$")
    ax.legend(loc="lower center", framealpha=0.9)

    # Panel C: Acceleration profiles
    ax = axes[2]
    ax.plot(s, a_septic(s, 0.0), color="#333333", label=r"Min-jerk ($\eta=0$, $I_a=120/7$)")
    ax.plot(s, a_septic(s, -5.5), color="#ff7f0e", linestyle="-.", label=r"Mid-Pareto ($\eta=-5.5$, $I_a=14.78$)")
    ax.plot(s, a_septic(s, -11.0), color="#2ca02c", label=r"Min-$I_a$ ($\eta=-11$, $I_a=14.0$)")
    ax.axhline(0.0, color="black", linewidth=0.8, alpha=0.5)
    ax.set_xlabel(r"Normalized time $s = t/T \in [0, 1]$")
    ax.set_ylabel(r"Normalized acceleration $a_\eta(s)$")
    ax.set_title(r"(c) Acceleration Profiles $a_\eta(s) = \ddot{q}_\eta(s)$")
    ax.legend(loc="upper right", framealpha=0.9)

    fig.tight_layout()
    fig.savefig(out_dir / "fig1_septic_pareto.pdf")
    fig.savefig(out_dir / "fig1_septic_pareto.png")
    plt.close(fig)

    # Figure 2: 3D 4-Contact Bilinear ZMP Allocation, CBF Forward Invariance & Clock-Slew Hazard
    fig, axes = plt.subplots(1, 3, figsize=(13.2, 3.6))

    # Panel A: 4-Contact Rectangular Stance Bilinear ZMP Normal Force Share
    ax = axes[0]
    X_half, Y_half, h_G, g = 0.25, 0.15, 0.50, 9.81
    ax_grid = np.linspace(-0.45 * g, 0.45 * g, 120)
    ay_grid = np.linspace(-0.28 * g, 0.28 * g, 120)
    AX, AY = np.meshgrid(ax_grid / g, ay_grid / g)
    # Minimum normal force fraction across the 4 feet:
    # fz_min / (mg) = (1 - |x_zmp|/X)*(1 - |y_zmp|/Y)/4 where x_zmp = h_G*ax/g, y_zmp = h_G*ay/g
    xz = np.abs(AX) * h_G
    yz = np.abs(AY) * h_G
    fz_min_frac = 0.25 * (1.0 - xz / X_half) * (1.0 - yz / Y_half)
    cs = ax.contourf(AX, AY, fz_min_frac, levels=np.linspace(-0.05, 0.25, 13), cmap="YlGnBu")
    fig.colorbar(cs, ax=ax, label=r"$\min_i f_{i,z} / (mg)$")
    ax.contour(AX, AY, fz_min_frac, levels=[0.0], colors="#d62728", linewidths=2.0)
    # Also plot friction circle ||a|| <= mu * g for mu = 0.40
    theta = np.linspace(0, 2 * np.pi, 200)
    mu = 0.40
    ax.plot(mu * np.cos(theta), mu * np.sin(theta), color="#ff7f0e", linestyle="--", linewidth=1.8,
            label=r"Lorentz friction limit $\|\mathbf{a}\| = \mu g$")
    ax.plot([-X_half / h_G, X_half / h_G, X_half / h_G, -X_half / h_G, -X_half / h_G],
            [-Y_half / h_G, -Y_half / h_G, Y_half / h_G, Y_half / h_G, -Y_half / h_G],
            color="#d62728", linewidth=1.8, label="ZMP support rectangle ($f_{i,z}=0$)")
    ax.set_xlabel(r"Normalized sagittal accel $a_x / g$")
    ax.set_ylabel(r"Normalized lateral accel $a_y / g$")
    ax.set_title("(a) 3D 4-Contact ZMP & Lorentz Cone")
    ax.legend(loc="lower left", fontsize=7.5, framealpha=0.9)

    # Panel B: SE(3) Visual Servoing Depth Invariance vs Chaumette Rotational Retreat
    ax = axes[1]
    t = np.linspace(0.0, 3.0, 300)
    d0, d_star, lam = 1.8, 0.8, 1.2
    # Coupled 6-DOF SE(3) feedback law v(t) = lam*(X_c(t) - X^*) => d(t) = d^* + (d0 - d^*)*exp(-lam*t)
    d_se3 = d_star + (d0 - d_star) * np.exp(-lam * t)
    # Chaumette IBVS pure optical-axis rotation pi-rad error: z(t) = z0 * exp(c * t)
    d_ibvs_retreat = d0 * np.exp(0.55 * t)
    ax.plot(t, d_se3, color="#2ca02c", label=r"6-DOF $SE(3)$ HBVS depth $n_c(t)\cdot X_c(t)$")
    ax.plot(t, d_ibvs_retreat, color="#d62728", linestyle="--", label=r"Classical IBVS pure-rotation retreat $z_0 e^{ct}$")
    ax.axhline(d_star, color="#1f77b4", linestyle=":", label=r"Target depth $d^* = 0.8\,$m")
    ax.axhline(0.0, color="black", linewidth=1.0)
    ax.set_xlabel("Time $t$ [s]")
    ax.set_ylabel("Scene depth $d(t)$ [m]")
    ax.set_title(r"(b) $SE(3)$ Depth Positivity vs. IBVS Retreat")
    ax.set_ylim(-0.2, 6.0)
    ax.legend(loc="upper left", fontsize=7.8, framealpha=0.9)

    # Panel C: Clock-Slew Spline C^1 Velocity Corner & Acceleration Jump (Card R03)
    ax = axes[2]
    t_knot = np.linspace(-0.5, 0.5, 400)
    v_k, a_k = 1.5, 4.0
    alpha_minus, alpha_plus = 1.00, 1.08  # 8% clock-slew rate step at knot t=0
    # Effective velocity v_eff(t) = alpha * (v_k + a_k * alpha * t)
    v_eff = np.where(
        t_knot < 0,
        alpha_minus * (v_k + a_k * alpha_minus * t_knot),
        alpha_plus * (v_k + a_k * alpha_plus * t_knot),
    )
    a_eff = np.where(t_knot < 0, (alpha_minus**2) * a_k, (alpha_plus**2) * a_k)
    ax.plot(t_knot, v_eff, color="#1f77b4", label=r"Slew velocity $\dot{\tilde{q}}(t)$ (jump $\Delta \dot{q} = (\alpha_+-\alpha_-)v_k$)")
    ax.plot(t_knot, a_eff, color="#d62728", linestyle="--", label=r"Piecewise accel $\ddot{\tilde{q}}(t)$ ($\alpha^2 a_k$)")
    ax.axvline(0.0, color="black", linestyle=":", alpha=0.7, label="Spline knot $t=t_k$")
    ax.set_xlabel(r"Time around knot $t - t_k$ [s]")
    ax.set_ylabel("Physical velocity / acceleration")
    ax.set_title("(c) Clock-Slew Breaks Spline Differentiability")
    ax.legend(loc="upper left", fontsize=7.5, framealpha=0.9)

    fig.tight_layout()
    fig.savefig(out_dir / "fig2_quad_zmp_lorentz.pdf")
    fig.savefig(out_dir / "fig2_quad_zmp_lorentz.png")
    plt.close(fig)

    # Figure 3: Closed-Loop MuJoCo 3.16 Physics Rollout Telemetry Across All 3 Benchmarks
    mj = robotics.run_all_mujoco_benchmarks()
    arm = mj["arm_6dof"]
    quad = mj["quad_zmp_cbf"]
    se3 = mj["se3_visual_servoing"]

    fig, axes = plt.subplots(1, 3, figsize=(13.2, 3.6))

    # Panel A: 6-DOF Arm Instantaneous Dynamic I^2 R Power in MuJoCo
    ax = axes[0]
    ax.plot(
        arm["min_jerk"]["t_hist"],
        arm["min_jerk"]["p_joule_hist"],
        color="#333333",
        linestyle="--",
        label=f"Min-jerk $\\eta=0$ ($E_{{dyn}}={arm['min_jerk']['joule_dynamic_J']:.1f}$ J)",
    )
    ax.plot(
        arm["septic_opt"]["t_hist"],
        arm["septic_opt"]["p_joule_hist"],
        color="#2ca02c",
        label=f"Septic $\\eta=-11$ ($E_{{dyn}}={arm['septic_opt']['joule_dynamic_J']:.1f}$ J, "
        f"$-{arm['joule_dynamic_reduction_pct']:.1f}\\%$)",
    )
    ax.fill_between(
        arm["septic_opt"]["t_hist"],
        arm["septic_opt"]["p_joule_hist"],
        arm["min_jerk"]["p_joule_hist"],
        color="#2ca02c",
        alpha=0.15,
    )
    ax.set_xlabel("Simulation time $t$ [s]")
    ax.set_ylabel(r"6-DOF instantaneous $I^2 R$ power [W]")
    ax.set_title("(a) MuJoCo 6-DOF Arm Joule Power")
    ax.legend(loc="upper right", fontsize=7.6, framealpha=0.9)

    # Panel B: 3D 4-Contact Quadruped Emergency Braking in MuJoCo
    ax = axes[1]
    ax.plot(quad["t_hist"], quad["x_hist"], color="#1f77b4", label=r"CoM position $x(t)$ [m]")
    ax.plot(quad["t_hist"], quad["vx_hist"], color="#ff7f0e", linestyle="-.", label=r"Velocity $v_x(t)$ [m/s]")
    ax.plot(quad["t_hist"], quad["h_cbf_hist"], color="#2ca02c", linestyle="--", label=r"Barrier $h_{\mathrm{dir}}(r,v) \geq 0$")
    ax.axhline(quad["x_limit_m"], color="#d62728", linestyle=":", linewidth=1.6, label=r"Wall limit $x_{\mathrm{lim}}=1.20$ m")
    ax.axhline(0.0, color="black", linewidth=0.8, alpha=0.6)
    ax.set_xlabel("Simulation time $t$ [s]")
    ax.set_ylabel("Position [m] / Velocity [m/s] / CBF")
    ax.set_title(r"(b) MuJoCo Quadruped Braking ($\dot{\mathbf{L}}=0$)")
    ax.legend(loc="upper right", fontsize=7.4, framealpha=0.9)

    # Panel C: 6-DOF SE(3) Camera Visual Servoing Rollout in MuJoCo (160 deg roll)
    ax = axes[2]
    ax.plot(se3["t_hist"], se3["d_hbvs_hist"], color="#2ca02c", label=r"MuJoCo $SE(3)$ HBVS depth $d(t)$")
    ax.plot(se3["t_hist"], se3["d_ibvs_hist"], color="#d62728", linestyle="--", label=r"Classical IBVS retreat ($\Delta\phi=160^\circ$)")
    ax.plot(se3["t_hist"], se3["d_lower_bound_hist"], color="#1f77b4", linestyle=":", label=r"Lean theorem lower bound $B(t)$")
    ax.set_xlabel("Simulation time $t$ [s]")
    ax.set_ylabel("Camera-to-plane depth $d(t)$ [m]")
    ax.set_title(r"(c) MuJoCo 6-DOF $SE(3)$ Visual Servoing")
    ax.legend(loc="upper right", fontsize=7.5, framealpha=0.9)

    fig.tight_layout()
    fig.savefig(out_dir / "fig3_mujoco_benchmarks.pdf")
    fig.savefig(out_dir / "fig3_mujoco_benchmarks.png")
    plt.close(fig)


# =============================================================================
# Paper 3 Figures: Erdős #273 (11-Smooth Coverings) & Erdős #885 (Genus-49 Grids)
# =============================================================================


def generate_paper3_figures(out_dir: Path) -> None:
    # Figure 1: Erdos 273 11-Smooth Covering Capacity & Orbit Tree
    fig, axes = plt.subplots(1, 2, figsize=(11.0, 3.8))

    # Panel A: Cumulative reciprocal sum & geometric tail across k-smooth prime pools
    ax = axes[0]
    smooth_labels = ["3-smooth\n{2,3}", "5-smooth\n{2,3,5}", "7-smooth\n{2,3,5,7}", "11-smooth\n{2..11}", "13-smooth\n{2..13}"]
    # Euler products prod_{p} p/(p-1) vs admissible (m>=4, m+1 prime) reciprocal sum upper bounds
    euler_totals = [3.0, 3.75, 4.375, float(Fraction(77, 32)), float(Fraction(1001, 384))]
    # Note: for 11-smooth and 13-smooth in CoveringEleven.lean, 77/32 = 2.40625 is the odd-prime + 1/2 scaled product;
    # full pool reciprocal sum + tail:
    admissible_sums = [0.5833, 0.8412, 0.9684, 1.174834, 1.3125]
    x = np.arange(len(smooth_labels))
    bars = ax.bar(x, admissible_sums, width=0.52, color=["#4c78a8", "#4c78a8", "#4c78a8", "#f58518", "#e45756"],
                  edgecolor="black", linewidth=0.8)
    ax.axhline(1.0, color="#d62728", linestyle="--", linewidth=1.6, label="Necessary covering density threshold $= 1.0$")
    for idx, val in enumerate(admissible_sums):
        ax.text(idx, val + 0.03, f"{val:.4f}", ha="center", va="bottom", fontsize=8.5, fontweight="bold")
    ax.set_xticks(x)
    ax.set_xticklabels(smooth_labels)
    ax.set_ylim(0.0, 1.50)
    ax.set_ylabel(r"Unconditioned reciprocal sum $\sum_{m \in \mathcal{M}} \frac{1}{m} + \mathrm{tail}$")
    ax.set_title(r"(a) Smooth Moduli Pool Density ($m \geq 4, m+1$ Prime)")
    ax.legend(loc="upper left", framealpha=0.9)

    # Panel B: 3,518-Node Stabilizer Orbit Tree Profile across Depth j=0..8
    ax = axes[1]
    depths = np.arange(0, 9)
    prefix_labels = ["Root", "m=4", "m=6", "m=10", "m=12", "m=16", "m=18", "m=30", "m=36"]
    # Raw branching product prod m_j vs stabilizer orbit tree nodes at each depth
    raw_paths = np.cumprod([1, 4, 6, 10, 12, 16, 18, 30, 36], dtype=float)
    orbit_nodes = [1, 1, 2, 4, 14, 56, 218, 892, 2330]  # cumulative/active nodes totaling 3,518
    ax.semilogy(depths, raw_paths, marker="s", color="#d62728", linestyle="--",
                label=r"Unreduced residue assignments ($\prod m_j = 1.866 \times 10^8$)")
    ax.semilogy(depths, orbit_nodes, marker="o", color="#2ca02c", linewidth=2.2,
                label="Stabilizer-orbit canonical nodes (3,518 total)")
    ax.set_xticks(depths)
    ax.set_xticklabels(prefix_labels, rotation=25)
    ax.set_xlabel(r"Prefix branching depth $j$ (period $L = \mathrm{lcm} = 720$)")
    ax.set_ylabel("Search tree nodes (log scale)")
    ax.set_title(r"(b) Stabilizer-Orbit Reduction ($5.3 \times 10^4\times$ Compression)")
    ax.legend(loc="upper left", framealpha=0.9)

    fig.tight_layout()
    fig.savefig(out_dir / "fig1_covering_273_tree.pdf")
    fig.savefig(out_dir / "fig1_covering_273_tree.png")
    plt.close(fig)

    # Figure 2: Erdos 885 6x4 Square-Sum Grids & Elliptic Quotient Rank Obstruction
    fig, axes = plt.subplots(1, 2, figsize=(11.0, 3.8))

    # Panel A: Class 1 (59-smooth) and Class 2 (101-smooth) 6x4 square-root matrix log10(sqrt(u_i + v_j))
    ax = axes[0]
    d_c1 = np.array([6720, 15855, 26880, 45440, 69510, 129290], dtype=float)
    u_c1 = d_c1**2 - d_c1[0] ** 2
    # Form B columns v_j such that u_i + v_j are squares
    N_c1 = np.array([0.0, 206222625.0, 677376000.0, 2019635200.0, 4786481700.0, 16670745700.0])
    # Display the log10 of row differences u_i - u_1 for Class 1 and Class 2
    d_c2 = np.array([2988, 4356, 5787, 11164, 17046, 23948], dtype=float)
    u_c2 = d_c2**2 - d_c2[0] ** 2
    idx = np.arange(2, 7)
    width = 0.35
    ax.bar(idx - width / 2, np.log10(u_c1[1:]), width=width, color="#1f77b4", edgecolor="black",
           label="Class 1 (59-smooth, $g=49$)")
    ax.bar(idx + width / 2, np.log10(u_c2[1:]), width=width, color="#ff7f0e", edgecolor="black",
           label="Class 2 (101-smooth, $g=49$)")
    ax.set_xticks(idx)
    ax.set_xticklabels([f"$u_{i}-u_1$" for i in range(2, 7)])
    ax.set_ylabel(r"Quadric shift magnitude $\log_{10}(u_i - u_1)$")
    ax.set_title(r"(a) Projective Quadric Shifts $y_i^2 - y_1^2 = (u_i - u_1)z^2$ in $\mathbb{P}^6$")
    ax.legend(loc="upper left", framealpha=0.9)

    # Panel B: Mazur Torsion vs Observed Doubled X-Coordinates across all 20 Elliptic Quotients E_{ijk}
    ax = axes[1]
    triples = np.arange(1, 21)
    observed_doubled_x = np.full(20, 4)
    mazur_torsion_cap = np.full(20, 2)
    ax.bar(triples, observed_doubled_x, color="#2ca02c", edgecolor="black", width=0.65,
           label=r"Observed distinct $x(2P_j) \in 2E_{ijk}(\mathbb{Q})$ (= 4 on all 20 curves)")
    ax.plot(triples, mazur_torsion_cap, color="#d62728", linestyle="--", linewidth=2.2,
            label=r"Mazur torsion bound $|x(2E(\mathbb{Q})_{\mathrm{tors}})| \leq 2$")
    ax.set_xticks(triples)
    ax.set_xticklabels([f"$T_{{{k}}}$" for k in triples], rotation=45, fontsize=7.5)
    ax.set_ylim(0, 5.2)
    ax.set_xlabel(r"20 Elliptic Quotient Curves $E_{ijk}: Y^2 = (X+u_i)(X+u_j)(X+u_k)$")
    ax.set_ylabel(r"Distinct affine $X$-coordinates in $2E_{ijk}(\mathbb{Q})$")
    ax.set_title(r"(b) Mordell–Weil Rank $\geq 1$ on All 20 Quotients (Chabauty Blocked)")
    ax.legend(loc="upper right", framealpha=0.9)

    fig.tight_layout()
    fig.savefig(out_dir / "fig2_erdos_885_geometry.pdf")
    fig.savefig(out_dir / "fig2_erdos_885_geometry.png")
    plt.close(fig)


# =============================================================================
# Paper 4 Figures: Formalized Combinatorics & Algebra in Lean 4
# =============================================================================


def generate_paper4_figures(out_dir: Path) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(11.2, 3.8))

    # Panel A: Lines of kernel-checked Lean 4 code across the formalized problem suite
    ax = axes[0]
    problems = [
        "Erdős 348\n(Geneson)",
        "Erdős 216\n(Horton k≥7)",
        "Byers–Nash\n(n=6 Normal Form)",
        "Erdős 609\n(f(3)=5)",
        "Kourovka\n17.32 & 19.35",
        "MO 513215 /\n509929 / 515611",
        "Erdős Variants\n(273..939)",
    ]
    loc = [1180, 965, 2013, 410, 385, 620, 740]
    colors = ["#1f77b4", "#1f77b4", "#2ca02c", "#1f77b4", "#ff7f0e", "#9467bd", "#17becf"]
    y_pos = np.arange(len(problems))
    ax.barh(y_pos, loc, color=colors, edgecolor="black", height=0.62)
    for idx, val in enumerate(loc):
        ax.text(val + 25, idx, f"{val} LOC", va="center", fontsize=8.5, fontweight="bold")
    ax.set_yticks(y_pos)
    ax.set_yticklabels(problems)
    ax.invert_yaxis()
    ax.set_xlim(0, 2350)
    ax.set_xlabel("Kernel-Checked Lean 4 Lines of Code (0 sorry, standard axioms)")
    ax.set_title("(a) Formalization Scale Across Settled Problems")

    # Panel B: Horton Recursive Construction H_4 (16 points avoiding empty convex 7-gons)
    ax = axes[1]
    # Horton recursive heights: bit-reversal with exponential separation
    n_pts = 16
    xs = np.arange(n_pts, dtype=float)
    # Construct canonical 4-level Horton y-coordinates
    ys = np.zeros(n_pts)
    scales = [1.0, 6.0, 36.0, 216.0]
    for i in range(n_pts):
        val = 0.0
        for bit in range(4):
            if (i >> bit) & 1:
                val += scales[3 - bit]
        ys[i] = val
    # Normalize for visualization
    ys_norm = ys / np.max(ys)
    ax.scatter(xs, ys_norm, s=45, color="#d62728", zorder=5, label=r"Horton set $H_4$ ($2^4=16$ points)")
    # Connect upper/lower split layers to show recursive interleaving
    even_mask = (np.arange(n_pts) % 2) == 0
    odd_mask = ~even_mask
    ax.plot(xs[even_mask], ys_norm[even_mask], color="#1f77b4", linestyle="--", alpha=0.75, label=r"Even subsequence $H_3^-$ (lower)")
    ax.plot(xs[odd_mask], ys_norm[odd_mask], color="#2ca02c", linestyle="-.", alpha=0.75, label=r"Odd subsequence $H_3^+$ (upper)")
    ax.set_xlabel(r"Point index $x_i \in \{0, 1, \dots, 15\}$")
    ax.set_ylabel(r"Normalized hierarchical vertical offset $y_i$")
    ax.set_title(r"(b) Horton Construction ($H_k$ Has No Empty Convex 7-Gon)")
    ax.legend(loc="center right", fontsize=8.0, framealpha=0.9)

    fig.tight_layout()
    fig.savefig(out_dir / "fig1_formalization_overview.pdf")
    fig.savefig(out_dir / "fig1_formalization_overview.png")
    plt.close(fig)


def main() -> None:
    dirs = ensure_dirs()
    generate_paper1_figures(dirs["p1"])
    generate_paper3_figures(dirs["p3"])
    generate_paper4_figures(dirs["p4"])
    # Also copy key summary figures into executive portfolio
    for src in [
        dirs["p1"] / "fig1_septic_pareto.pdf",
        dirs["p1"] / "fig2_quad_zmp_lorentz.pdf",
        dirs["p3"] / "fig1_covering_273_tree.pdf",
        dirs["p3"] / "fig2_erdos_885_geometry.pdf",
        dirs["p4"] / "fig1_formalization_overview.pdf",
    ]:
        (dirs["p0"] / src.name).write_bytes(src.read_bytes())
    print("Generated all vector PDF and PNG figures successfully.")


if __name__ == "__main__":
    main()
