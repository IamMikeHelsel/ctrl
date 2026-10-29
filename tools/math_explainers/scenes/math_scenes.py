"""Sectioned Manim explanations driven by the exact experiment artifact."""

import json
from fractions import Fraction
from pathlib import Path

import numpy as np
from manim import (
    Axes,
    Create,
    DashedLine,
    Dot,
    FadeIn,
    FadeOut,
    Line,
    Rectangle,
    VGroup,
    VMobject,
    Write,
)

from story import BLUE, GREEN, INK, MUTED, ORANGE, StoryScene, words

ROOT = Path(__file__).resolve().parents[3]
REPORT = json.loads((ROOT / "site/explainers/lab/results.json").read_text())
DATA = {row["id"]: row for row in REPORT["experiments"]}


def number(value):
    return float(Fraction(value))


class MathScene(StoryScene):
    def setup(self):
        super().setup()
        self.source_derivation = {"id": "math-explainers-144", "sha256": REPORT["sha256"]}

    def clear_board(self):
        objects = [
            obj for obj in self.mobjects if obj is not self.footer and obj is not self.mobjects[0]
        ]
        if objects:
            self.play(*[FadeOut(obj) for obj in objects], run_time=0.5)


class LyapunovWalkthrough(MathScene):
    story_id = "lyapunov-energy"
    story_title = "Length can grow while energy falls"
    summary = "A scalar warmup, then an exact rational 2D certificate."
    category = "Stability / exact example"

    def construct(self):
        d = DATA["lyapunov"]
        self.step(
            "Start with one number",
            "For a = 4/5, each step multiplies x by 4/5 and V = x² by 16/25. The certificate requires |a| < 1.",
        )
        formula = words("x(next) = a x      V(x) = x²", 35).move_to([0, 1.8, 0])
        self.play(Write(formula))
        rate = next(Fraction(r["a"]) for r in d["scalar"] if r["a"] == "4/5")
        bars = VGroup()
        for k in range(6):
            h = 2.8 * float(rate ** (2 * k))
            bar = Rectangle(width=0.65, height=h, color=GREEN, fill_opacity=0.35).move_to(
                [-4 + k * 1.6, -1.7 + h / 2, 0]
            )
            caption = words(f"k={k}", 20).move_to([-4 + k * 1.6, -2.1, 0])
            bars.add(bar, caption)
            self.play(FadeIn(bar), FadeIn(caption), run_time=0.65)
        self.hold(2)
        self.step(
            "The ordinary length can grow",
            "In the 2D example, x₀ = (1, 0) becomes (1, -0.35). Squared length rises from 1 to 449/400. This does not disprove stability.",
        )
        self.clear_board()
        samples = d["samples"]
        axes = Axes(
            x_range=[-1.3, 1.3, 0.5],
            y_range=[-0.9, 0.9, 0.5],
            x_length=5.6,
            y_length=4,
            axis_config={"color": MUTED, "include_ticks": False},
        ).move_to([-3, -0.15, 0])
        self.play(Create(axes))
        dots = VGroup(
            *[
                Dot(axes.c2p(*[number(t) for t in row["x"]]), color=ORANGE if i == 0 else BLUE)
                for i, row in enumerate(samples[:2])
            ]
        )
        arrow = Line(dots[0].get_center(), dots[1].get_center(), color=BLUE)
        values = (
            VGroup(
                words("A = [ 1       3/5 ]", 29),
                words("     [ -7/20  3/5 ]", 29),
                words("length²: 1 → 449/400", 27, ORANGE),
            )
            .arrange([0, -1, 0], buff=0.45)
            .move_to([3.25, 0, 0])
        )
        self.play(FadeIn(dots), Create(arrow), Write(values))
        self.hold(3)
        self.step(
            "Choose a different energy",
            "SymPy solves P - AᵀPA = I exactly. P is positive definite by its positive leading principal minors. Along this trajectory V loses exactly the previous squared length.",
        )
        self.play(FadeOut(values))
        P = np.array([[number(t) for t in row] for row in d["P"]])
        chol = np.linalg.cholesky(P)
        for row in [samples[0], samples[3], samples[7]]:
            v = number(row["energy"])
            coords = [
                np.sqrt(v) * np.linalg.solve(chol.T, [np.cos(t), np.sin(t)])
                for t in np.linspace(0, 2 * np.pi, 100)
            ]
            curve = VMobject(color=GREEN, stroke_width=1.3).set_points_as_corners(
                [axes.c2p(*p) for p in coords]
            )
            self.play(Create(curve), run_time=0.5)
        path = VMobject(color=BLUE).set_points_as_corners(
            [axes.c2p(*[number(t) for t in row["x"]]) for row in samples]
        )
        vals = (
            VGroup(
                words("P - Aᵀ P A = I", 32, GREEN),
                words("V(next) = V(x) - length²", 26),
                words(
                    f"V: {samples[0]['display_energy']:.3f} → {samples[1]['display_energy']:.3f}",
                    28,
                    GREEN,
                ),
            )
            .arrange([0, -1, 0], buff=0.5)
            .move_to([3.2, 0, 0])
        )
        self.play(Create(path), Write(vals), run_time=2.5)
        self.hold(3)
        self.step(
            "Know what carries the conclusion",
            "The existing Lean theorem assumes both quadratic forms are positive and proves convergence. These plots are finite examples. SymPy is checking this certificate's algebra, not re-proving the theorem or validating a robot.",
        )
        self.clear_board()
        final = (
            VGroup(
                words("Positive energy", 35, GREEN),
                words("+ positive loss at every nonzero state", 29, GREEN),
                words("⇒ convergence in the stated linear model", 30),
                words("Lean: tendsto_pow_mulVec_zero", 23, MUTED),
                words("Example arithmetic: SymPy + exact fractions", 23, MUTED),
            )
            .arrange([0, -1, 0], buff=0.5)
            .move_to([0, 0, 0])
        )
        self.play(Write(final), run_time=2)
        self.hold(4)


class BrakingWalkthrough(MathScene):
    story_id = "braking-budget"
    story_title = "Delay consumes a calculable distance"
    summary = "Build the stopping envelope, then change one assumption."
    category = "Braking / model sensitivity"

    def construct(self):
        d = DATA["braking"]["example"]
        scale, origin = 12, -5

        def bar(start, amount, color):
            return Rectangle(
                width=amount * scale, height=0.7, color=color, fill_opacity=0.35
            ).move_to([origin + (start + amount / 2) * scale, 0, 0])

        error, reaction, brake = [
            number(d[k]) for k in ("error", "delay_distance", "brake_distance")
        ]
        self.step(
            "Declare the uncertainty",
            "This example assumes a forward point mass, speed at most 1.1 m/s and position error at most 0.02 m. Braking authority is at least 2 m/s² after the delay.",
        )
        labels = words("u = 1.1 m/s     ε = 0.02 m     b = 2 m/s²", 30).move_to([0, 1.9, 0])
        ebar = bar(0, error, ORANGE)
        self.play(Write(labels), FadeIn(ebar))
        self.play(Write(words("position uncertainty", 25, ORANGE).move_to([-3.5, -1.05, 0])))
        self.hold(2.5)
        self.step(
            "Motion continues during the delay",
            "With τ = 0.20 s and forward acceleration at most 1 m/s², reaction travel is uτ + Aτ²/2 = 0.24 m. Speed can reach 1.3 m/s before braking begins.",
        )
        self.play(
            FadeIn(bar(error, reaction, BLUE)),
            Write(words(f"reaction: {reaction:.4f} m", 28, BLUE).move_to([0, 1, 0])),
            run_time=1.5,
        )
        self.hold(3)
        self.step(
            "Brake from the later speed",
            "Braking from 1.3 m/s requires 0.4225 m. Together with the earlier terms, required clearance is 0.6825 m. The 0.5 m wall lies inside this envelope.",
        )
        self.play(FadeIn(bar(error + reaction, brake, GREEN)), run_time=1.5)
        wall = DashedLine(
            [origin + 0.5 * scale, -0.8, 0], [origin + 0.5 * scale, 0.8, 0], color=ORANGE
        )
        self.play(
            Create(wall),
            Write(words("wall: 0.5 m", 25, ORANGE).move_to([origin + 0.5 * scale, -1.3, 0])),
            Write(words(f"total: {number(d['distance']):.4f} m", 32).move_to([0, 2.55, 0])),
        )
        self.hold(4)
        self.step(
            "Change a bound, then validate it",
            "With every other input fixed, reducing delay from 0.20 s to 0.18 s saves exactly 38.7 mm. That is model sensitivity, not a measured system improvement. A rejected admission does not stop the robot.",
        )
        self.clear_board()
        summary = VGroup(
            words("D = ε + uτ + Aτ²/2 + (u + Aτ)²/(2b)", 29),
            words("dD/dτ = (u + Aτ)(1 + A/b)", 30, BLUE),
            words(
                f"20 ms less delay → {1000 * number(d['saved_by_20ms']):.1f} mm less clearance",
                30,
                GREEN,
            ),
            words("Validate the clock, actuator and braking bounds.", 26, MUTED),
        ).arrange([0, -1, 0], buff=0.65)
        self.play(Write(summary), run_time=2)
        self.hold(4)


class KalmanWalkthrough(MathScene):
    story_id = "kalman-balance"
    story_title = "The gain balances two errors"
    summary = "Complete the square, find the gain, test an assumption."
    category = "Estimation / scalar variance"

    def construct(self):
        d = DATA["kalman"]["example"]
        p, r, gain = [number(d[k]) for k in ("p", "r", "gain")]
        self.step(
            "Mix two uncertain estimates",
            "The scalar model has prior error variance p = 1 and measurement error variance r = 4, with zero cross-covariance. Gain k weights the measurement.",
        )
        setup = (
            VGroup(
                words("estimate = (1-k) prior + k measurement", 31),
                words("p = 1       r = 4       cross-covariance = 0", 28, BLUE),
            )
            .arrange([0, -1, 0], buff=0.7)
            .move_to([0, 0.8, 0])
        )
        self.play(Write(setup), run_time=2)
        self.hold(2.5)
        self.step(
            "Compare the resulting variance",
            "Variance is (1-k)²p + k²r. For these inputs, a half-and-half blend has variance 1.25; k = 0.2 gives 0.8. All plotted gains share one scale.",
        )
        self.play(FadeOut(setup))
        axes = Axes(
            x_range=[0, 1, 0.2],
            y_range=[0, 4, 1],
            x_length=7.2,
            y_length=3.8,
            axis_config={"color": MUTED, "include_numbers": False},
        ).move_to([-0.5, -0.15, 0])
        curve = axes.plot(lambda k: (1 - k) ** 2 * p + k**2 * r, x_range=[0, 1], color=BLUE)
        self.play(
            Create(axes),
            Create(curve),
            Write(words("gain k: 0 → 1", 23).move_to([0, -2.5, 0])),
            Write(words("variance: 0 → 4", 23).move_to([0, 2.3, 0])),
        )
        self.play(
            FadeIn(Dot(axes.c2p(gain, number(d["variance"])), color=GREEN)),
            Write(words("(0.2, 0.8)", 25, GREEN).move_to([-2.2, -0.5, 0])),
        )
        self.hold(3)
        self.step(
            "Complete the square",
            "SymPy verifies variance = pr/(p+r) + (p+r)(k-p/(p+r))². Since p+r is positive, the square exposes the unique optimal gain for this objective.",
        )
        self.clear_board()
        formula = VGroup(
            words("variance = pr/(p+r) + (p+r)(k-p/(p+r))²", 29),
            words("minimum + nonnegative excess", 30, GREEN),
            words("k* = p/(p+r) = 1/5", 34, BLUE),
        ).arrange([0, -1, 0], buff=0.75)
        self.play(Write(formula), run_time=2)
        self.hold(3)
        self.step(
            "Test the missing cross term",
            "If the cross-covariance is 1/2, an extra 2k(1-k)c term changes the optimum to 1/8. The independent-error formula cannot certify the correlated model.",
        )
        self.clear_board()
        warning = VGroup(
            words("When c ≠ 0, add 2k(1-k)c", 32, ORANGE),
            words("k* = (p-c)/(p+r-2c)", 33),
            words("p=1, r=4, c=1/2 → k*=1/8", 30, BLUE),
            words("Check the error model before trusting the gain.", 26, MUTED),
        ).arrange([0, -1, 0], buff=0.65)
        self.play(Write(warning), run_time=2)
        self.hold(4)
