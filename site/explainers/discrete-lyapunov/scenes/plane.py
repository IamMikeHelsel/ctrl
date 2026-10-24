"""Harder example: a 2D system whose Euclidean norm grows on some steps.

A has spectral radius 0.9 but operator norm about 1.17. P solves A^T P A - P = -I.
Left: the state plane with V's level sets (accent) and the unit circle (warn, dashed).
Right: |x_k| (not monotone) and V(x_k) (monotone, under rho^k V(x_0)).
All numbers come from ../example.py.

Render: uv run --no-project --python 3.12 --with manim==0.22.0 --with numpy \
    tools/explainer/render.py discrete-lyapunov --scene PlaneLyapunov
"""

import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve()
sys.path[:0] = [str(HERE.parents[4] / "tools" / "explainer"), str(HERE.parents[1])]

from example import OP_NORM, RHO, SPECTRAL_RADIUS, P, V, level_set, trajectory  # noqa: E402
from explainer_style import (  # noqa: E402
    ACCENT,
    GRID,
    MUTED,
    TEXT,
    WARN,
    ExplainerScene,
    eq,
    label,
)
from manim import (  # noqa: E402
    DOWN,
    LEFT,
    RIGHT,
    UP,
    UR,
    Axes,
    Circle,
    Create,
    DashedVMobject,
    Dot,
    FadeIn,
    FadeOut,
    Line,
    VGroup,
    VMobject,
    Write,
)

ORIGIN_PLANE = np.array([-3.55, -0.35, 0.0])
SCALE = 1.45  # scene units per state unit
XS = trajectory()
NORMS = np.linalg.norm(XS, axis=1)
VS = np.array([V(x) for x in XS])


def to_plane(x) -> np.ndarray:
    return ORIGIN_PLANE + SCALE * np.array([x[0], x[1], 0.0])


def ellipse(v: float, color: str, width: float, opacity: float) -> VMobject:
    pts = [to_plane(p) for p in level_set(v)]
    m = VMobject(stroke_color=color, stroke_width=width, stroke_opacity=opacity)
    m.set_points_as_corners(pts + [pts[0]])
    return m


class PlaneLyapunov(ExplainerScene):
    POSTER_AT = 0.7

    def construct(self):
        self.title_card(
            "When the plain norm is the wrong ruler",
            f"2D system: spectral radius {SPECTRAL_RADIUS:.2f}, but the norm of A is {OP_NORM:.2f}",
        )

        # Left: the plane.
        axes = VGroup(
            Line(ORIGIN_PLANE + LEFT * 2.6, ORIGIN_PLANE + RIGHT * 2.6, color=GRID),
            Line(ORIGIN_PLANE + DOWN * 2.6, ORIGIN_PLANE + UP * 2.6, color=GRID),
        )
        unit = DashedVMobject(
            Circle(radius=SCALE, color=WARN, stroke_width=2.5).move_to(ORIGIN_PLANE),
            num_dashes=48,
        )
        unit_lab = label("unit circle", 18, WARN).next_to(
            ORIGIN_PLANE + SCALE * np.array([0.72, 0.72, 0]), UR, buff=0.08
        )
        system = eq(r"x_{k+1} = A\,x_k", size=34).to_corner(UP + LEFT, buff=0.45)
        self.play(Create(axes), Write(system))
        self.play(Create(unit), FadeIn(unit_lab))
        self.say("Dashed: points with plain length 1.")

        # Right: two small charts.
        kmax = len(XS) - 1
        ax_n = Axes(
            x_range=[0, kmax, 2],
            y_range=[0, 1.2, 0.5],
            x_length=5.4,
            y_length=2.1,
            axis_config={"color": GRID, "include_ticks": False},
            tips=False,
        ).move_to(RIGHT * 3.55 + UP * 1.5)
        ax_v = Axes(
            x_range=[0, kmax, 2],
            y_range=[0, 6, 2],
            x_length=5.4,
            y_length=2.1,
            axis_config={"color": GRID, "include_ticks": False},
            tips=False,
        ).move_to(RIGHT * 3.55 + DOWN * 1.35)
        lab_n = eq(r"\lVert x_k \rVert", size=28, color=WARN).next_to(ax_n, UP, buff=0.12)
        lab_v = eq(r"V(x_k) = x_k^{\top} P\, x_k", size=28, color=ACCENT).next_to(
            ax_v, UP, buff=0.12
        )
        one = DashedVMobject(
            Line(ax_n.c2p(0, 1), ax_n.c2p(kmax, 1), color=WARN, stroke_width=1.5), num_dashes=30
        )
        one_lab = label("1", 16, WARN).next_to(ax_n.c2p(0, 1), LEFT, buff=0.12)
        k_lab = label("step k", 16, MUTED).next_to(ax_v, DOWN, buff=0.12)
        envelope = ax_v.plot(
            lambda k: RHO**k * VS[0], x_range=[0, kmax], color=MUTED, stroke_width=1.5
        )
        env = DashedVMobject(envelope, num_dashes=40)
        env_lab = eq(rf"\rho^k V(x_0),\ \rho = {RHO:.3f}", size=22, color=MUTED).next_to(
            ax_v.c2p(kmax * 0.62, RHO ** (kmax * 0.62) * VS[0]), UP + RIGHT, buff=0.05
        )
        self.play(FadeIn(VGroup(ax_n, ax_v, lab_n, lab_v, one, one_lab, k_lab)))

        # The certificate.
        cert = eq(
            r"P \approx \begin{bmatrix}"
            + rf" {P[0, 0]:.2f} & {P[0, 1]:.2f} \\ {P[1, 0]:.2f} & {P[1, 1]:.2f} "
            + r"\end{bmatrix},\quad P - A^{\top} P A = I \succ 0",
            size=26,
        ).next_to(system, DOWN, aligned_edge=LEFT, buff=0.25)
        self.play(FadeIn(cert))
        self.say("Lyapunov's ruler: P, found by solving one linear equation.", hold=1.5)

        # Step through the trajectory.
        dots_n, dots_v, rings = VGroup(), VGroup(), VGroup()
        state = Dot(to_plane(XS[0]), color=TEXT, radius=0.08)
        ring = ellipse(VS[0], ACCENT, 3.0, 1.0)
        self.play(Create(ring), FadeIn(state))
        rings.add(ring)
        dots_n.add(Dot(ax_n.c2p(0, NORMS[0]), color=WARN, radius=0.05))
        dots_v.add(Dot(ax_v.c2p(0, VS[0]), color=ACCENT, radius=0.05))
        self.play(FadeIn(dots_n), FadeIn(dots_v), run_time=0.4)

        for k in range(1, len(XS)):
            slow = k <= 2
            trail = Line(
                to_plane(XS[k - 1]),
                to_plane(XS[k]),
                color=TEXT,
                stroke_width=1.5,
                stroke_opacity=0.5,
            )
            new_ring = ellipse(VS[k], ACCENT, 2.2, 0.9)
            dn = Dot(ax_n.c2p(k, NORMS[k]), color=WARN, radius=0.05)
            dv = Dot(ax_v.c2p(k, VS[k]), color=ACCENT, radius=0.05)
            seg_n = Line(ax_n.c2p(k - 1, NORMS[k - 1]), dn.get_center(), color=WARN, stroke_width=2)
            seg_v = Line(ax_v.c2p(k - 1, VS[k - 1]), dv.get_center(), color=ACCENT, stroke_width=2)
            self.play(
                state.animate.move_to(to_plane(XS[k])),
                Create(trail),
                rings[-1].animate.set_stroke(width=1.2, opacity=0.35),
                Create(new_ring),
                Create(seg_n),
                FadeIn(dn),
                Create(seg_v),
                FadeIn(dv),
                run_time=1.1 if slow else 0.45,
            )
            rings.add(new_ring)
            if k == 1:
                self.say(
                    f"Step 1: length goes UP, {NORMS[0]:.2f} to {NORMS[1]:.2f}. "
                    f"V goes down, {VS[0]:.2f} to {VS[1]:.2f}.",
                    hold=3,
                )
            elif k == 2:
                self.say("Every step lands on a smaller ellipse. The length wobbles.")
            elif k == 6:
                self.say("Length rises again on later steps. V never does.")

        self.play(Create(env), FadeIn(env_lab))
        self.say("V stays under a geometric envelope, so the state goes to zero.", hold=1.5)
        badge = self.theorem_badge("ControlsLean.Controls.tendsto_pow_mulVec_zero", hold=3)
        self.play(FadeOut(badge))
        self.say("A good P turns a wobbly path into a steady downhill one.", hold=2.5)
