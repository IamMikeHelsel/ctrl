"""Shared visual style for theorem-explainer manim scenes.

Every explainer scene imports from here so videos look like one series and match the
site's dark theme (site/style.css). Sans-serif everywhere: Inter for text, LaTeX
`sansmath` for equations.

Rules this module encodes (see .claude/skills/theorem-explainer/SKILL.md):
  * Colors carry meaning. ACCENT = the certified object (the Lyapunov level set, the
    barrier, the bound). WARN = a conventional or naive quantity. BAD = the hypothesis
    failing. MUTED = scaffolding (axes, grids, labels).
  * Text is short. A caption is one line. An equation is one idea.
  * Every moving quantity is computed from the math (numpy), never hand-tweened.

Typical use:

    import sys, pathlib
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[4] / "tools" / "explainer"))
    from explainer_style import *

    class MyScene(ExplainerScene):
        def construct(self):
            self.title_card("A plain claim", "model / assumptions / no hardware claim")
            ...
            self.theorem_badge("ControlsLean.Controls.tendsto_pow_mulVec_zero")
"""

from __future__ import annotations

from manim import (
    DOWN,
    LEFT,
    UP,
    FadeIn,
    FadeOut,
    MathTex,
    RoundedRectangle,
    Scene,
    Text,
    TexTemplate,
    VGroup,
    config,
)

__all__ = [
    "ACCENT",
    "ACCENT_SOFT",
    "BAD",
    "BG",
    "BLUE",
    "FONT",
    "GRID",
    "MONO",
    "MUTED",
    "SURFACE",
    "SURFACE_ALT",
    "TEXT",
    "WARN",
    "ExplainerScene",
    "caption",
    "eq",
    "label",
    "mono",
    "sans_tex_template",
]

# Palette: mirrors the dark tokens in site/style.css.
BG = "#0d1513"
SURFACE = "#131e1b"
SURFACE_ALT = "#1c2c27"
TEXT = "#edf5f1"
MUTED = "#b0c2b9"
GRID = "#34483f"
ACCENT = "#72d8bb"  # certified quantity
ACCENT_SOFT = "#1d3e32"
WARN = "#f1be83"  # naive / conventional quantity
BAD = "#f08e87"  # hypothesis fails
BLUE = "#8fb8f0"  # neutral second series

FONT = "Inter"
MONO = "DejaVu Sans Mono"

config.background_color = BG


def sans_tex_template() -> TexTemplate:
    """LaTeX template whose math and text are sans-serif."""
    tpl = TexTemplate()
    tpl.add_to_preamble(
        r"\usepackage[T1]{fontenc}"
        r"\usepackage{sansmath}\sansmath"
        r"\renewcommand{\familydefault}{\sfdefault}"
    )
    return tpl


_TEX = sans_tex_template()


def eq(tex: str, size: float = 40, color: str = TEXT, **kw) -> MathTex:
    """One equation, sans-serif. Pass several strings via `kw['parts']` for coloring."""
    parts = kw.pop("parts", None)
    if parts:
        return MathTex(*parts, tex_template=_TEX, font_size=size, color=color, **kw)
    return MathTex(tex, tex_template=_TEX, font_size=size, color=color, **kw)


def label(s: str, size: float = 26, color: str = TEXT, weight: str = "NORMAL") -> Text:
    return Text(s, font=FONT, font_size=size, color=color, weight=weight)


def caption(s: str, size: float = 22) -> Text:
    return Text(s, font=FONT, font_size=size, color=MUTED)


def mono(s: str, size: float = 18, color: str = MUTED) -> Text:
    return Text(s, font=MONO, font_size=size, color=color)


class ExplainerScene(Scene):
    """Base scene: background, title card, captions, and a Lean theorem badge."""

    def setup(self):
        self.camera.background_color = BG
        self._caption = None

    def title_card(self, title: str, subtitle: str | None = None, hold: float = 2.0):
        t = label(title, size=40, weight="MEDIUM")
        group = VGroup(t)
        if subtitle:
            group.add(caption(subtitle, size=22))
        group.arrange(DOWN, buff=0.3)
        self.play(FadeIn(group, shift=0.2 * UP))
        self.wait(hold)
        self.play(FadeOut(group))

    def say(self, s: str, hold: float = 0.0):
        """Replace the bottom caption. One short line."""
        new = caption(s).to_edge(DOWN, buff=0.45)
        if self._caption is None:
            self.play(FadeIn(new), run_time=0.5)
        else:
            self.play(FadeOut(self._caption), FadeIn(new), run_time=0.5)
        self._caption = new
        if hold:
            self.wait(hold)

    def clear_caption(self):
        if self._caption is not None:
            self.play(FadeOut(self._caption), run_time=0.4)
            self._caption = None

    def theorem_badge(self, lean_name: str, hold: float = 2.5):
        """Badge naming the Lean theorem behind what is on screen.

        Sits in the caption zone (bottom center) and clears the caption first, so it never
        covers the figure.
        """
        self.clear_caption()
        txt = mono(lean_name, size=17, color=ACCENT)
        tag = label("Proved in Lean", size=15, color=MUTED)
        inner = VGroup(tag, txt).arrange(DOWN, aligned_edge=LEFT, buff=0.08)
        box = RoundedRectangle(
            corner_radius=0.08,
            width=inner.width + 0.4,
            height=inner.height + 0.3,
            fill_color=SURFACE,
            fill_opacity=0.92,
            stroke_color=GRID,
            stroke_width=1.5,
        )
        badge = VGroup(box, inner.move_to(box)).to_edge(DOWN, buff=0.3)
        self.play(FadeIn(badge, shift=0.1 * UP), run_time=0.5)
        self.wait(hold)
        return badge
