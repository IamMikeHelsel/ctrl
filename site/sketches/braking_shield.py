"""Manim sketch: closed-form Lorentz-cone CBF braking shield for a 4-contact robot.

Every plotted quantity comes from the theorem-backed kernels in
``ctrl.robotics.contact_cbf``; nothing on screen is hand-animated.

Render (from the repo root):
    uv run --with manim manim -qh site/sketches/braking_shield.py BrakingShield
"""

from __future__ import annotations

import math

from manim import (
    BLUE_C,
    DOWN,
    GREEN_C,
    GREY_B,
    GREY_D,
    LEFT,
    ORANGE,
    RED_C,
    RIGHT,
    UP,
    YELLOW_C,
    Arrow,
    Axes,
    DashedLine,
    Dot,
    FadeIn,
    Line,
    Rectangle,
    Scene,
    Text,
    ValueTracker,
    VGroup,
    Write,
    always_redraw,
    linear,
)

from ctrl.robotics.contact_cbf import (
    CentroidalQuadParams,
    directional_cbf,
    quad_contact_forces,
    safe_decel_max,
    lorentz_cbf_safety_filter,
)

PARAMS = CentroidalQuadParams(m=12.0, g=9.81, h_g=0.30, w_x=0.20, w_y=0.12, mu=0.60)
A_MAX = safe_decel_max(PARAMS.g, PARAMS.mu, PARAMS.w_x, PARAMS.h_g)
A_BRAKE = 0.9 * A_MAX
X_LIM = 1.20
ALPHA = 6.0
A_FWD = 2.0
V0 = 1.5
DT = 1e-3
# Past ~1.45 s the robot sits within 0.3 mm of the wall at v ≈ 0, where the barrier
# no longer constrains acceleration and λ* chatters at the sample rate.
T_END = 1.4

N_HAT = (1.0, 0.0, 0.0)
R_LIM = (X_LIM, 0.0, 0.0)


def simulate() -> list[dict[str, float]]:
    """Shielded and unshielded rollouts of the front-bumper position x(t)."""
    x, v = 0.0, V0
    xg, vg = 0.0, V0
    rows = []
    for k in range(int(T_END / DT) + 1):
        h = directional_cbf(R_LIM, (x, 0.0, 0.0), (v, 0.0, 0.0), N_HAT, A_BRAKE)
        # dh/dt + ALPHA h >= 0  <=>  (-v / a_brake) * a >= v - ALPHA h
        a_cbf = (-v / A_BRAKE, 0.0, 0.0)
        b = v - ALPHA * h
        lam, u_safe = lorentz_cbf_safety_filter(a_cbf, b, (A_FWD, 0.0, 0.0), (-A_BRAKE, 0.0, 0.0))
        ax = u_safe[0]
        rows.append({"t": k * DT, "x": x, "v": v, "h": h, "lam": lam, "ax": ax, "xg": xg, "vg": vg})
        v += ax * DT
        x += v * DT
        if xg < X_LIM:
            vg += A_FWD * DT
            xg = min(X_LIM, xg + vg * DT)
    return rows


ROWS = simulate()


def at(t: float) -> dict[str, float]:
    return ROWS[min(len(ROWS) - 1, max(0, round(t / DT)))]


# World (metres) -> screen for the side-view stage.
S = 4.2
X0 = -5.9
GROUND_Y = -0.35


def wx(x: float) -> float:
    return X0 + S * x


def side_forces(t: float) -> tuple[tuple[float, float], tuple[float, float]]:
    """Rear and front (fx, fz), summed over the left/right foot pairs."""
    f = quad_contact_forces(PARAMS, at(t)["ax"], 0.0)
    rear = (f[(-1, -1)][0] + f[(-1, 1)][0], f[(-1, -1)][2] + f[(-1, 1)][2])
    front = (f[(1, -1)][0] + f[(1, 1)][0], f[(1, -1)][2] + f[(1, 1)][2])
    return rear, front


class BrakingShield(Scene):
    def construct(self) -> None:
        t = ValueTracker(0.0)

        title = Text("Solver-free braking shield", font_size=34).to_corner(UP + LEFT)
        sub = Text(
            "closed-form CBF  ·  4-foot ZMP allocation  ·  Lorentz friction cones",
            font_size=20,
            color=GREY_B,
        ).next_to(title, DOWN, aligned_edge=LEFT, buff=0.12)

        ground = Line([wx(-0.25), GROUND_Y, 0], [wx(1.45), GROUND_Y, 0], color=GREY_B)
        wall = Rectangle(width=0.18, height=2.2, color=RED_C, fill_opacity=0.5, stroke_width=0)
        wall.move_to([wx(X_LIM) + 0.09, GROUND_Y + 1.1, 0])
        wall_lbl = Text("x_lim = 1.20 m", font_size=18, color=RED_C).next_to(wall, UP, buff=0.1)

        body_w, body_h = 2 * PARAMS.w_x * S, 0.32
        hip_h = PARAMS.h_g * S

        def body_at(x_front: float, color, opacity: float) -> VGroup:
            cx = wx(x_front) - body_w / 2
            torso = Rectangle(width=body_w, height=body_h, color=color, fill_opacity=opacity)
            torso.move_to([cx, GROUND_Y + hip_h, 0])
            legs = VGroup(
                *[
                    Line([cx + s * body_w / 2, GROUND_Y + hip_h, 0], [cx + s * body_w / 2, GROUND_Y, 0], color=color)
                    for s in (-1, 1)
                ]
            )
            com = Dot([cx, GROUND_Y + hip_h, 0], radius=0.05, color=color)
            return VGroup(torso, legs, com)

        ghost = always_redraw(lambda: body_at(at(t.get_value())["xg"], GREY_D, 0.15))
        ghost_lbl = always_redraw(
            lambda: Text(
                "unshielded" if at(t.get_value())["xg"] < X_LIM else "impact",
                font_size=16,
                color=GREY_B if at(t.get_value())["xg"] < X_LIM else RED_C,
            ).next_to(ghost, DOWN, buff=0.12)
        )
        robot = always_redraw(lambda: body_at(at(t.get_value())["x"], BLUE_C, 0.45))

        cone_len = 1.1
        half = math.atan(PARAMS.mu)

        def cones_and_forces() -> VGroup:
            row = at(t.get_value())
            cx = wx(row["x"]) - body_w / 2
            rear, front = side_forces(t.get_value())
            g = VGroup()
            for foot_x, (fx, fz) in ((cx - body_w / 2, rear), (cx + body_w / 2, front)):
                base = [foot_x, GROUND_Y, 0]
                for sgn in (-1, 1):
                    tip = [foot_x + sgn * cone_len * math.sin(half), GROUND_Y + cone_len * math.cos(half), 0]
                    g.add(DashedLine(base, tip, color=GREEN_C, stroke_width=2, dash_length=0.06))
                k = 0.011
                g.add(
                    Arrow(
                        base,
                        [foot_x + k * fx, GROUND_Y + k * fz, 0],
                        buff=0,
                        color=YELLOW_C,
                        stroke_width=5,
                        max_tip_length_to_length_ratio=0.12,
                    )
                )
            return g

        forces = always_redraw(cones_and_forces)

        legend = VGroup(
            Text("— — friction cone  |f_t| ≤ μ f_z", font_size=16, color=GREEN_C),
            Text("→ contact force (bilinear ZMP + shear)", font_size=16, color=YELLOW_C),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08)
        legend.next_to(ground, DOWN, buff=0.45).align_to(ground, LEFT)

        # Right-hand math panel.
        panel = VGroup(
            Text("Barrier", font_size=20, color=ORANGE),
            Text("h = (x_lim − x) − v² / (2·a_brake)", font_size=18),
            Text("Closed-form filter (no QP)", font_size=20, color=ORANGE),
            Text("u = (1 − λ*)·u_nom + λ*·π_brake", font_size=18),
            Text("λ* = clip((b − a·u_nom) / (a·π − a·u_nom), 0, 1)", font_size=16),
            Text("Safe deceleration (proved biconditional)", font_size=20, color=ORANGE),
            Text(f"a_max = min(μ, W/h_G)·g = {A_MAX:.2f} m/s²", font_size=18),
            Text("Lean 4: lorentz_backup_controller_safe,", font_size=15, color=GREY_B),
            Text("Lean 4: quad_contact_in_lorentz_cone", font_size=15, color=GREY_B),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        panel.to_corner(UP + RIGHT, buff=0.35)

        def live_readout() -> VGroup:
            row = at(t.get_value())
            return VGroup(
                Text(f"t = {row['t']:.2f} s", font_size=18),
                Text(f"x = {row['x']:.3f} m    v = {row['v']:.2f} m/s", font_size=18),
                Text(f"h = {row['h']:.3f}    λ* = {row['lam']:.2f}", font_size=18, color=YELLOW_C),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(panel, DOWN, aligned_edge=LEFT, buff=0.3)

        readout = always_redraw(live_readout)

        # Bottom plots: barrier h(t) and blend λ*(t).
        def make_axes(y_range, label: str, color) -> tuple[Axes, Text]:
            ax = Axes(
                x_range=[0, T_END, 0.5],
                y_range=y_range,
                x_length=5.6,
                y_length=1.3,
                tips=False,
                axis_config={"color": GREY_B, "stroke_width": 2, "include_ticks": False},
            )
            lbl = Text(label, font_size=18, color=color)
            return ax, lbl

        h_ax, h_lbl = make_axes([0, 1.25, 0.25], "h(t) ≥ 0  (barrier)", BLUE_C)
        l_ax, l_lbl = make_axes([0, 1.05, 0.5], "λ*(t)  (how much brake)", YELLOW_C)
        h_ax.to_corner(DOWN + LEFT, buff=0.45)
        l_ax.to_corner(DOWN + RIGHT, buff=0.45)
        h_lbl.next_to(h_ax, UP, aligned_edge=LEFT, buff=0.08)
        l_lbl.next_to(l_ax, UP, aligned_edge=LEFT, buff=0.08)

        def trace(axes: Axes, key: str, color):
            def f():
                tv = max(t.get_value(), 2 * DT)
                return axes.plot(lambda s: at(s)[key], x_range=[0, tv, 0.01], color=color, stroke_width=3)

            return always_redraw(f)

        h_curve = trace(h_ax, "h", BLUE_C)
        l_curve = trace(l_ax, "lam", YELLOW_C)

        self.play(Write(title), FadeIn(sub))
        self.play(FadeIn(ground), FadeIn(wall), FadeIn(wall_lbl), FadeIn(panel, shift=LEFT * 0.3))
        self.add(ghost, ghost_lbl, robot, forces)
        self.play(FadeIn(legend), FadeIn(h_ax), FadeIn(l_ax), FadeIn(h_lbl), FadeIn(l_lbl))
        self.add(h_curve, l_curve, readout)
        self.wait(0.5)
        self.play(t.animate.set_value(T_END), run_time=8, rate_func=linear)

        final = at(T_END)
        verdict = Text(
            f"{1000 * (X_LIM - final['x']):.1f} mm from the wall · every foot inside its cone · no solver",
            font_size=22,
            color=GREEN_C,
        ).move_to([0, -1.6, 0])
        self.play(FadeIn(verdict, shift=UP * 0.2))
        self.wait(2.5)
