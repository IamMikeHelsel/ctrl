"""Manim explanation for the latency-braking study. AI-assisted.

Render: uv run --no-project --python 3.12 --with manim==0.22.0 manim -ql --format=mp4 \
  --media_dir output/manim experiments/research/latency_braking_scene.py LatencyBraking
The animation illustrates the exact 273/400 m example. No hardware footage.
"""

from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Create,
    Dot,
    FadeIn,
    FadeOut,
    Line,
    Scene,
    Text,
    ValueTracker,
    VGroup,
    always_redraw,
    linear,
)


class LatencyBraking(Scene):
    def construct(self):
        self.camera.background_color = "#101a25"
        title = Text("A stopping rule needs a clock", font_size=34).to_edge(UP)
        subtitle = Text(
            "One-dimensional model / supplied bounds / no hardware claim",
            font_size=17,
            color="#b8c6d3",
        ).next_to(title, DOWN)
        self.play(FadeIn(title), FadeIn(subtitle))
        inputs = (
            VGroup(
                Text("Speed estimate: 1.0 +/- 0.1 m/s", font_size=23),
                Text("Position error: 0.02 m   |   Delay: 0.20 s", font_size=23),
                Text("Acceleration during delay: 1 m/s^2   |   Brake: 2 m/s^2", font_size=21),
            )
            .arrange(DOWN, aligned_edge=LEFT)
            .shift(UP * 0.6)
        )
        self.play(FadeIn(inputs))
        self.wait(2)
        self.play(FadeOut(inputs))
        nominal = Text("Instantaneous rule: 0.2500 m", font_size=27, color="#a7d8ce").shift(UP)
        bounded = Text("Including delay + uncertainty: 0.6825 m", font_size=27, color="#f1be83")
        wall_text = Text("Available clearance: 0.5000 m", font_size=24).shift(DOWN)
        self.play(FadeIn(nominal), FadeIn(bounded), FadeIn(wall_text))
        self.wait(3)
        self.play(FadeOut(nominal), FadeOut(bounded), FadeOut(wall_text))
        track = Line(LEFT * 5, RIGHT * 5, color="#65798c").shift(DOWN * 0.4)
        wall_x = -5 + 10 * 0.5 / 0.8
        wall = Line([wall_x, -1, 0], [wall_x, 0.6, 0], color="#f08e87")
        wall_label = Text("wall: 0.50 m", font_size=20, color="#f08e87").next_to(wall, DOWN)
        time = ValueTracker(0)

        def position(t):
            if t <= 0.2:
                return 0.02 + 1.1 * t + t * t / 2
            s = min(t - 0.2, 0.65)
            return 0.26 + 1.3 * s - s * s

        robot = always_redraw(
            lambda: Dot(
                [-5 + 10 * position(time.get_value()) / 0.8, -0.4, 0], color="#a7d8ce", radius=0.13
            )
        )
        phase = Text("Delay, then brake to rest", font_size=27).shift(UP)
        self.play(Create(track), Create(wall), FadeIn(wall_label), FadeIn(robot), FadeIn(phase))
        self.play(time.animate.set_value(0.2), run_time=2, rate_func=linear)
        self.play(time.animate.set_value(0.85), run_time=4, rate_func=linear)
        result = Text("Stops beyond the wall at 0.6825 m", font_size=25, color="#f1be83").shift(
            DOWN * 2
        )
        self.play(FadeIn(result))
        self.wait(2)
        self.play(FadeOut(VGroup(track, wall, wall_label, robot, phase, result)))
        conclusion = VGroup(
            Text("The bounded rule rejects this admission.", font_size=29),
            Text("Rejection does not repair an already-moving robot.", font_size=23),
            Text(
                "Next: validate bounds, backup feasibility and implementation.",
                font_size=20,
                color="#b8c6d3",
            ),
        ).arrange(DOWN, buff=0.35)
        self.play(FadeIn(conclusion))
        self.wait(3)
