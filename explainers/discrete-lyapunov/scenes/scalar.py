"""Simple example: x_{k+1} = a x_k with V(x) = x^2.

Render: uv run --no-project --python 3.12 --with manim==0.22.0 --with numpy \
    tools/explainer/render.py discrete-lyapunov --scene ScalarLyapunov
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve()
sys.path[:0] = [str(HERE.parents[4] / "tools" / "explainer"), str(HERE.parents[1])]

from example import A_SCALAR, A_SCALAR_BAD  # noqa: E402
from explainer_style import (  # noqa: E402
    ACCENT,
    BAD,
    MUTED,
    ExplainerScene,
    eq,
    label,
)
from manim import (  # noqa: E402
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Create,
    DashedVMobject,
    Dot,
    FadeIn,
    FadeOut,
    NumberLine,
    Rectangle,
    VGroup,
    Write,
)

STEPS = 8
BAR_W = 0.42
BAR_UNIT = 0.6  # scene units per unit of V; one uncapped scale for both cases


class ScalarLyapunov(ExplainerScene):
    POSTER_AT = 0.44  # fraction of runtime used for the poster frame

    def construct(self):
        self.title_card("One number, one rule", "the scalar case of the discrete Lyapunov theorem")

        rule = eq(r"x_{k+1} = a\,x_k", size=44)
        energy = eq(r"V(x) = x^2", size=44)
        step = eq(r"V(x_{k+1}) = a^2\, V(x_k)", size=44)
        VGroup(rule, energy, step).arrange(RIGHT, buff=0.9).to_edge(UP, buff=0.5)
        self.play(Write(rule))
        self.say("A state that is multiplied by a each step.")
        self.play(Write(energy))
        self.say("Measure its size with V. Here P = 1, so V is the square.")
        self.play(Write(step))
        self.say("One step multiplies V by a squared. No estimate needed.", hold=1.5)

        self.run_case(A_SCALAR, ACCENT, good=True)
        self.run_case(A_SCALAR_BAD, BAD, good=False)

        summary = VGroup(
            eq(r"P > 0 \quad\text{and}\quad P - A^{\top} P A > 0", size=40),
            eq(
                r"\Longrightarrow\quad V(x_{k+1}) \le \rho\, V(x_k)"
                r"\ \text{ for some } \rho < 1",
                size=40,
            ),
        ).arrange(DOWN, buff=0.4)
        self.play(FadeOut(VGroup(rule, energy, step)), FadeIn(summary))
        self.say("The theorem is the same idea for a matrix A and a matching P.", hold=2.5)
        badge = self.theorem_badge("ControlsLean.Controls.exists_lyapunov_contraction", hold=3)
        self.play(FadeOut(summary), FadeOut(badge))

    def run_case(self, a: float, color: str, good: bool):
        self.clear_caption()
        margin = 1 - a * a
        head = eq(
            rf"a = {a:g}:\quad P - a^2 P = 1 - {a * a:.2f} = {margin:.2f}",
            size=36,
            color=color,
        ).shift(UP * 1.55)
        verdict = label("> 0, certificate holds" if good else "< 0, no certificate", 24, color)
        verdict.next_to(head, DOWN, buff=0.2)
        self.play(FadeIn(head), FadeIn(verdict))

        line = NumberLine(
            x_range=[-0.2, 2.4, 0.2], length=6.2, color=MUTED, include_numbers=False
        ).shift(LEFT * 3.3 + DOWN * 0.1)
        ticks = VGroup(
            *[label(f"{v:g}", 16, MUTED).next_to(line.n2p(v), DOWN, buff=0.15) for v in (0, 1, 2)]
        )
        xlab = eq(r"x_k", size=26, color=MUTED).next_to(line, UP, buff=0.25).align_to(line, LEFT)
        base = DOWN * 2.75 + RIGHT * 0.6
        axis = DashedVMobject(
            Rectangle(width=STEPS * (BAR_W + 0.12) + 0.3, height=0.001, color=MUTED), num_dashes=40
        ).move_to(base + RIGHT * (STEPS * (BAR_W + 0.12)) / 2)
        vlab = eq(r"V(x_k)", size=26, color=MUTED).next_to(axis, LEFT, buff=0.25)
        self.play(Create(line), FadeIn(ticks), FadeIn(xlab), FadeIn(axis), FadeIn(vlab))

        x = 1.0
        dot = Dot(line.n2p(x), color=color, radius=0.1)
        self.play(FadeIn(dot))
        bars = VGroup()
        for k in range(STEPS + 1):
            v = x * x
            h = v * BAR_UNIT
            bar = Rectangle(
                width=BAR_W,
                height=max(h, 0.01),
                fill_color=color,
                fill_opacity=0.85,
                stroke_width=0,
            )
            bar.move_to(base + RIGHT * (0.3 + k * (BAR_W + 0.12)), aligned_edge=DOWN)
            bars.add(bar)
            self.play(FadeIn(bar, shift=0.1 * UP), run_time=0.35)
            if k == 0:
                self.say("Start at x = 1, so V = 1.")
            elif k == 1:
                self.say(f"Each step multiplies V by {a * a:.2f}. Here V goes 1, then {v:.2f}, ...")
            x_next = a * x
            if k < STEPS and line.x_range[0] <= x_next <= line.x_range[1]:
                self.play(dot.animate.move_to(line.n2p(x_next)), run_time=0.45)
            x = x_next

        tail = (
            f"V shrinks by {a * a:.2f} every step, so x goes to 0."
            if good
            else f"V grows by {a * a:.2f} every step. Here the state does run away."
        )
        self.say(tail, hold=2.2)
        self.play(FadeOut(VGroup(head, verdict, line, ticks, xlab, axis, vlab, dot, bars)))
